From New.generatedproof.github_com.sanjit_bhat.pav Require Import advrpc server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  serde server.

(* notes:
- BlameUnknown is like giving up.
it gives the caller a trivial postcond.
since the request might not have even hit the serv, it's not in front of a Q.
- the specs implicitly assume a good network pipeline to good serv.
under those conditions, the RPC client should encode args correctly,
the RPC server should decode args correctly,
the RPC server should encode replies correctly,
and the RPC client should decode replies correctly.
the specs capture this by not allowing errors from RPC serde. *)

Module server.
Import serde.server server.server.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

(* TODO: make [is_rpc_cli] generic. currently, specialized to server. *)
Definition is_rpc_cli (c : loc) (good : option cfg.t) : iProp Σ :=
  match good with None => True | Some γ => is_inv γ end.

#[global] Instance is_rpc_cli_pers c good : Persistent (is_rpc_cli c good).
Proof. apply _. Qed.

(* TODO: trusted good param. *)
Lemma wp_Dial (good : option cfg.t) (addr : w64) :
  {{{ is_pkg_init advrpc }}}
  @! advrpc.Dial #addr
  {{{
    ptr_cli, RET #ptr_cli;
    "#His_cli" ∷ is_rpc_cli ptr_cli good
  }}}.
Proof. Admitted.

Lemma wp_CallPut c good uid sl_pk pk ver :
  {{{
    is_pkg_init server ∗
    "#His_cli" ∷ is_rpc_cli c good ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "#His_put" ∷ match good with None => True | Some γ =>
      ∃ i uidγ,
      "%Hlook_uidγ" ∷ ⌜γ.(cfg.uidγ) !! uid = Some uidγ⌝ ∗
      "#Hidx" ∷ mono_list_idx_own uidγ i (ver, pk) end
  }}}
  @! server.CallPut #c #uid #sl_pk #ver
  {{{ RET #(); True }}}.
Proof. Admitted.

Lemma wp_History_cli_call (Q : cfg.t → state.t → iProp Σ)
    c good sl_arg d0 arg ptr_reply (x : slice.t) :
  {{{
    is_pkg_init server ∗
    "#His_cli" ∷ is_rpc_cli c good ∗
    "Hsl_arg" ∷ sl_arg ↦*{d0} arg ∗
    "Hptr_reply" ∷ ptr_reply ↦ x ∗
    "#Hfupd" ∷ match good with None => True | Some γ =>
      □ (|={⊤,∅}=> ∃ σ, own γ σ ∗ (own γ σ ={∅,⊤}=∗ Q γ σ)) end
  }}}
  c @ (ptrT.id advrpc.Client.id) @ "Call" server.HistoryRpc #sl_arg #ptr_reply
  {{{
    sl_reply err0, RET #err0;
    "Hsl_arg" ∷ sl_arg ↦*{d0} arg ∗
    "Hptr_reply" ∷ ptr_reply ↦ sl_reply ∗

    "Herr_net" ∷ match err0 with true => True | false =>
    ∃ replyB,
    "Hsl_reply" ∷ sl_reply ↦* replyB ∗

    "Hgood" ∷ match good with None => True | Some γ =>
    ∃ chainProof linkSig hist bound err1,
    "%His_reply" ∷ ⌜HistoryReply.wish replyB
      (HistoryReply.mk' chainProof linkSig hist bound err1) []⌝ ∗

    (* align with serv rpc rcvr, which doesn't know encoded args in precond. *)
    (("%Herr_serv_dec" ∷ ⌜err1 = true⌝ ∗
      "Hgenie" ∷ ¬ ⌜∃ obj tail, HistoryArg.wish arg obj tail⌝) ∨

    ∃ uid prevEpoch prevVerLen tail σ lastDig lastKeys,
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "%Hdec" ∷ ⌜HistoryArg.wish arg
      (HistoryArg.mk' uid prevEpoch prevVerLen) tail⌝ ∗
    "HQ" ∷ Q γ σ ∗
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗

    "#Herr_serv_args" ∷
      match err1 with
      | true => ⌜uint.nat prevEpoch ≥ numEps ∨
        uint.nat prevVerLen > length pks⌝
      | false =>
        ∃ lastLink,
        "%Hnoof_epochs" ∷ ⌜numEps = sint.nat (W64 numEps)⌝ ∗
        "%Hnoof_vers" ∷ ⌜length pks = sint.nat (W64 (length pks))⌝ ∗
        "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗

        "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
          (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
          (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
        "#Hwish_hist" ∷ ktcore.wish_ListMemb γ.(cfg.vrf_pk) uid prevVerLen
          lastDig hist ∗
        "%Heq_hist" ∷ ⌜Forall2
          (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
          (drop (uint.nat prevVerLen) pks) hist⌝ ∗
        "#Hwish_bound" ∷ ktcore.wish_NonMemb γ.(cfg.vrf_pk) uid
          (W64 $ length pks) lastDig bound
      end) end end
  }}}.
Proof. Admitted.

Lemma wp_Audit_cli_call (Q : cfg.t → state.t → iProp Σ)
    c good sl_arg d0 arg ptr_reply (x : slice.t) :
  {{{
    is_pkg_init server ∗
    "#His_cli" ∷ is_rpc_cli c good ∗
    "Hsl_arg" ∷ sl_arg ↦*{d0} arg ∗
    "Hptr_reply" ∷ ptr_reply ↦ x ∗
    "#Hfupd" ∷ match good with None => True | Some γ =>
      □ (|={⊤,∅}=> ∃ σ, own γ σ ∗ (own γ σ ={∅,⊤}=∗ Q γ σ)) end
  }}}
  c @ (ptrT.id advrpc.Client.id) @ "Call" server.AuditRpc #sl_arg #ptr_reply
  {{{
    sl_reply err0, RET #err0;
    "Hsl_arg" ∷ sl_arg ↦*{d0} arg ∗
    "Hptr_reply" ∷ ptr_reply ↦ sl_reply ∗

    "Herr_net" ∷ match err0 with true => True | false =>
    ∃ replyB,
    "Hsl_reply" ∷ sl_reply ↦* replyB ∗

    "Hgood" ∷ match good with None => True | Some γ =>
    ∃ proofs err1,
    "%His_reply" ∷ ⌜AuditReply.wish replyB (AuditReply.mk' proofs err1) []⌝ ∗

    (("%Herr_serv_dec" ∷ ⌜err1 = true⌝ ∗
      "Hgenie" ∷ ¬ ⌜∃ obj tail, AuditArg.wish arg obj tail⌝) ∨

    ∃ prevEpoch tail σ,
    let numEps := length σ.(state.hist) in
    "%Hdec" ∷ ⌜AuditArg.wish arg (AuditArg.mk' prevEpoch) tail⌝ ∗
    "HQ" ∷ Q γ σ ∗
    "Herr" ∷
      match err1 with
      | true => ⌜uint.nat prevEpoch ≥ length σ.(state.hist)⌝
      | false =>
        "%Hnoof_eps" ∷ ⌜numEps = sint.nat (W64 $ numEps)⌝ ∗
        "%Hlen_proofs" ∷ ⌜(uint.Z prevEpoch + length proofs + 1)%Z = numEps⌝ ∗

        "#His_upds" ∷ ([∗ list] i ↦ aud ∈ proofs,
          ∃ dig0 dig1,
          let predEp := (uint.nat prevEpoch + i)%nat in
          "%Hlook0" ∷ ⌜σ.(state.hist).*1 !! predEp = Some dig0⌝ ∗
          "%Hlook1" ∷ ⌜σ.(state.hist).*1 !! (S predEp) = Some dig1⌝ ∗
          "#His_upd" ∷ ktcore.wish_ListUpdate dig0 aud.(ktcore.AuditProof.Updates) dig1) ∗
        "#His_sigs" ∷ ([∗ list] i ↦ aud ∈ proofs,
          ∃ link,
          let ep := (uint.nat prevEpoch + S i)%nat in
          "#His_link" ∷ hashchain.is_chain (take (S ep) σ.(state.hist).*1)
            None link (S ep) ∗
          "#His_sig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk) (W64 ep) link aud.(ktcore.AuditProof.LinkSig))
      end) end end
  }}}.
Proof. Admitted.

Lemma wp_CallStart c good :
  {{{
    is_pkg_init server ∗
    "#His_cli" ∷ is_rpc_cli c good
  }}}
  @! server.CallStart #c
  {{{
    ptr_chain ptr_vrf err, RET (#ptr_chain, #ptr_vrf, #(ktcore.blame_to_u64 err));
    "%Hblame" ∷ ⌜ktcore.BlameSpec err {[ktcore.BlameServFull:=option_bool good]}⌝ ∗
    "#Herr" ∷ (if decide (err ≠ ∅) then True else
      ∃ chain vrf,
      "#Hptr_chain" ∷ StartChain.own ptr_chain chain (□) ∗
      "#Hptr_vrf" ∷ StartVrf.own ptr_vrf vrf (□) ∗

      "Hgood" ∷ match good with None => True | Some γ =>
        ∃ servHist last_link,
        let numEps := length servHist in
        "#Hlb_servHist" ∷ mono_list_lb_own γ.(cfg.histγ) servHist ∗
        "%Hnoof_eps" ∷ ⌜numEps = sint.nat (W64 $ numEps)⌝ ∗

        "%His_PrevEpochLen" ∷ ⌜uint.nat chain.(StartChain.PrevEpochLen) < numEps⌝ ∗
        "#His_PrevLink" ∷ hashchain.is_chain
          (take (uint.nat chain.(StartChain.PrevEpochLen)) servHist.*1)
          None chain.(StartChain.PrevLink)
          (uint.nat chain.(StartChain.PrevEpochLen)) ∗
        "%His_ChainProof" ∷ ⌜hashchain.wish_Proof chain.(StartChain.ChainProof)
          (drop (uint.nat chain.(StartChain.PrevEpochLen)) servHist.*1)⌝ ∗
        "#His_last_link" ∷ hashchain.is_chain servHist.*1 None
          last_link numEps ∗
        "#His_LinkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
          (W64 $ numEps - 1) last_link chain.(StartChain.LinkSig) ∗

        "%Heq_VrfPk" ∷ ⌜γ.(cfg.vrf_pk) = vrf.(StartVrf.VrfPk)⌝ ∗
        "#His_VrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.sig_pk) γ.(cfg.vrf_pk)
          vrf.(StartVrf.VrfSig) end)
    }}}.
Proof. Admitted.

End proof.
End server.
