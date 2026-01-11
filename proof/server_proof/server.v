From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang.goose.model.channel.protocol Require Import simple.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  serde.

From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module server.
Import serde.server.

(* gmap from uid's to list of pks (indexed by version). *)
Definition keys_ty := gmap w64 (list $ list w8).

(* FIXME: needed for lia to unify [length digs] terms where one has keys_ty and
the other has its unfolding *)
Global Hint Unfold keys_ty : word.

Module state.
Record t :=
  mk {
    (* pending map of all keys.
    client gives server permission to add to this.
    all writable post-conds only reference pending. *)
    pending: keys_ty;
    (* history of digs and keys.
    server can update this by adding dig that corresponds to curr pending.
    all read-only post-conds only reference hist. *)
    (* TODO: technically, can derive keys from dig,
    just like we derive link from digs in below specs.
    that would be a bit more work since a dig inverts to a merkle map,
    which requires a few more steps to connect to (uid, ver, pk). *)
    hist: list (list w8 * keys_ty);
  }.
End state.

Module cfg.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
    (* map from uid to gname. *)
    uidγ: gmap w64 gname;
    histγ: gname;
    (* for now, have sigpred GS be diff from serv.hist GS.
    serv.hist GS talks about keys, whereas auditor (sharing same sigpred),
    doesn't have the plaintext keys. *)
    sigpredγ: ktcore.sigpred_cfg.t;
  }.
End cfg.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

(** invariants. *)

Implicit Types γ : cfg.t.
Implicit Types σ : state.t.

Definition gs_inv γ σ : iProp Σ :=
  "#Hpend" ∷ ([∗ map] uid ↦ pks ∈ σ.(state.pending),
    ∃ uidγ,
    "%Hlook_uidγ" ∷ ⌜γ.(cfg.uidγ) !! uid = Some uidγ⌝ ∗
    "#Hpks" ∷ ([∗ list] ver ↦ pk ∈ pks,
      ∃ i,
      (* client owns mlist_auth for their uid.
      for adversarial uid, auth in inv. *)
      mono_list_idx_own uidγ i ((W64 ver), pk))) ∗
  (* client remembers lb's of this. *)
  "Hhist" ∷ mono_list_auth_own γ.(cfg.histγ) 1 σ.(state.hist).

Definition keys_sub : relation keys_ty := map_included (λ _, prefix).

(* TODO: unclear if we need to relate dig to keys in σ.(hist).
might be able to prove client correctness and serv specs without it.
note: serv can maintain inv that ties its merkle tree to both
lastDig and lastKeys. *)
Definition state_inv σ : iProp Σ :=
  "%Hpend" ∷ ⌜∀ lastKeys,
    last σ.(state.hist).*2 = Some lastKeys →
    keys_sub lastKeys σ.(state.pending)⌝ ∗
  "%Hhist" ∷ ⌜list_reln σ.(state.hist).*2 keys_sub⌝.

Axiom own_Server : ∀ γ σ, iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Definition serv_inv γ : iProp Σ :=
  ∃ σ,
  "Hserv" ∷ own_Server γ σ ∗
  "Hgs" ∷ gs_inv γ σ ∗
  "#Hstate" ∷ state_inv σ.

Definition is_serv_inv γ := inv nroot (serv_inv γ).

(* TODO: serv ptr [s] is unbound. *)
Definition is_Server (s : loc) γ : iProp Σ :=
  is_serv_inv γ.

Lemma hist_pks_prefix uid γ (i j : nat) (x y : list w8 * keys_ty) :
  i ≤ j →
  is_serv_inv γ -∗
  mono_list_idx_own γ.(cfg.histγ) i x -∗
  mono_list_idx_own γ.(cfg.histγ) j y ={⊤}=∗
  ⌜x.2 !!! uid `prefix_of` y.2 !!! uid⌝.
Proof.
  iIntros (?) "#His_serv #Hidx0 #Hidx1".
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iNamed "Hgs".
  iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx0") as %Hlook0.
  iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx1") as %Hlook1.
  iMod ("Hclose" with "[-]") as "_"; [iFrame "∗#"|].
  iNamed "Hstate".
  iIntros "!> !%".

  apply (list_lookup_fmap_Some_2 snd) in Hlook0, Hlook1.
  destruct x as [? keys0], y as [? keys1]. simpl in *.
  opose proof (list_reln_trans_refl _ _ Hhist
    _ _ _ _ Hlook0 Hlook1 ltac:(lia)) as Hsub.
  rewrite /keys_sub /map_included /map_relation in Hsub.
  specialize (Hsub uid).
  rewrite !lookup_total_alt.
  destruct (keys0 !! uid) eqn:Heq0;
    destruct (keys1 !! uid) eqn:Heq1;
    rewrite Heq0 Heq1 in Hsub |-*;
    simpl in *; try done.
  apply prefix_nil.
Qed.

Lemma put_op_records γ i x :
  is_serv_inv γ -∗
  mono_list_idx_own γ.(cfg.histγ) i x ={⊤}=∗
  ∀ uid pks,
    ⌜x.2 !! uid = Some pks⌝ -∗
    (* if empty pks, might not have uidγ. *)
    ⌜length pks > 0%nat⌝ -∗
    ∃ uidγ,
      ⌜γ.(cfg.uidγ) !! uid = Some uidγ⌝ ∗
      ([∗ list] ver ↦ pk ∈ pks,
        ∃ i,
        mono_list_idx_own uidγ i ((W64 ver), pk)).
Proof.
  iIntros "#His_serv #Hidx".
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iNamed "Hgs".
  iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %Hlook_hist.
  iMod ("Hclose" with "[-]") as "_"; [by iFrame "∗#"|].
  iNamed "Hstate".
  iModIntro.

  iIntros "* %Hlook_uid %Hlen_pks".
  apply (list_lookup_fmap_Some_2 snd) in Hlook_hist.
  destruct x as [? keys]. simpl in *.
  apply lookup_lt_Some in Hlook_hist as ?.
  list_elem (σ.(state.hist).*2) (pred (length σ.(state.hist).*2)) as lastKeys; [word|].
  opose proof (list_reln_trans_refl _ _ Hhist
    _ _ _ _ Hlook_hist HlastKeys_lookup ltac:(lia)) as Hsub0.
  rewrite -last_lookup in HlastKeys_lookup.
  apply Hpend in HlastKeys_lookup.
  assert (keys_sub keys σ.(state.pending)) as Hsub.
  { by trans lastKeys. }
  rewrite /keys_sub /map_included /map_relation in Hsub.
  specialize (Hsub uid).

  rewrite Hlook_uid in Hsub.
  destruct (σ.(state.pending) !! uid) as [pks0|] eqn:Hlook_pend;
    rewrite Hlook_pend in Hsub;
    simpl in *; try done.
  iDestruct (big_sepM_lookup with "Hpend") as "@"; [done|].
  apply prefix_to_take in Hsub as ->.
  by iDestruct (big_sepL_take with "Hpks") as "$".
Qed.

(** state transition ops. *)

Definition Q_read i γ σ : iProp Σ :=
  mono_list_lb_own γ.(cfg.histγ) σ.(state.hist) ∗
  ⌜i < length σ.(state.hist)⌝.

Lemma op_read γ i (a : list w8 * keys_ty) :
  is_serv_inv γ -∗
  mono_list_idx_own γ.(cfg.histγ) i a -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗ Q_read i γ σ)).
Proof.
  iIntros "#His_serv #Hidx".
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame "Hserv".
  iIntros "Hserv".
  iMod "Hmask" as "_".
  iNamed "Hgs".
  iDestruct (mono_list_lb_own_get with "Hhist") as "#Hlb".
  iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %?%lookup_lt_Some.
  iMod ("Hclose" with "[-]") as "_"; iFrame "∗#". word.
Qed.

Definition pure_put uid pk (ver : w64) (pend : keys_ty) :=
  let pks := pend !!! uid in
  (* drop put if not right version.
  this enforces a "linear" version history. *)
  if bool_decide (uint.nat ver ≠ length pks) then pend else
  <[uid:=pks ++ [pk]]>pend.

Lemma sub_over_put pend uid pk ver :
  keys_sub pend (pure_put uid pk ver pend).
Proof.
  rewrite /pure_put.
  case_bool_decide; [done|].
  rewrite /keys_sub.
  apply insert_included; [apply _|].
  rewrite lookup_total_alt.
  intros ? ->. simpl.
  by apply prefix_app_r.
Qed.

Lemma op_put γ uid uidγ i ver pk :
  is_serv_inv γ -∗
  ⌜γ.(cfg.uidγ) !! uid = Some uidγ⌝ -∗
  mono_list_idx_own uidγ i (ver, pk) -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    let σ' := set state.pending (pure_put uid pk ver) σ in
    (own_Server γ σ' ={∅,⊤}=∗ True)).
Proof.
  iIntros "#His_serv %Hlook_uidγ #Hmono_idx".
  iModIntro.
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame "Hserv".
  iIntros "Hserv".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); [|done].
  iModIntro.
  iFrame.

  destruct σ. simpl in *.
  iSplitL.
  - iNamed "Hgs". iFrame.
    rewrite /pure_put /=.
    case_bool_decide; [iFrame "#"|].
    iApply big_sepM_insert_2; [|iFrame "#"].
    iFrame "%".
    iApply big_sepL_snoc.
    iSplit.
    2: { iExists _. iExactEq "Hmono_idx". repeat f_equal. word. }
    rewrite lookup_total_alt.
    destruct (pending !! uid) eqn:Hlook;
      rewrite Hlook; simpl; [|done].
    iDestruct (big_sepM_lookup with "Hpend") as "@"; [done|].
    by simplify_eq/=.
  - iNamed "Hstate".
    iSplit; iPureIntro; simpl; [|done].
    intros.
    trans pending; [naive_solver|].
    apply sub_over_put.
Qed.

Lemma op_add_hist γ dig :
  is_serv_inv γ -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    let σ' := set (state.hist) (.++ [(dig, σ.(state.pending))]) σ in
    (own_Server γ σ' ={∅,⊤}=∗ True)).
Proof.
  iIntros "#His_serv".
  iModIntro.
  rewrite /is_Server.
  iInv "His_serv" as ">@" "Hclose".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iFrame "Hserv".
  iIntros "Hserv".
  iNamed "Hgs".
  iNamed "Hstate".
  iMod (mono_list_auth_own_update_app with "Hhist") as "[Hhist _]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-]"); [|done].
  iModIntro.
  iFrame "∗∗#".

  destruct σ. simpl in *.
  iSplit; iPureIntro; simpl.
  - intros ? Hlast.
    rewrite fmap_app last_snoc in Hlast.
    by simplify_eq/=.
  - rewrite fmap_app.
    by apply list_reln_snoc.
Qed.

End proof.

(** golang server state. *)

Module secrets.
Record t := mk' {
  commit : list w8;
}.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj γ : iProp Σ :=
  ∃ ptr_sig ptr_vrf sl_commit,
  "#Hstr_secrets" ∷ ptr ↦□ (server.secrets.mk ptr_sig ptr_vrf sl_commit) ∗
  "#Hown_sig" ∷ cryptoffi.own_sig_sk ptr_sig γ.(cfg.sig_pk)
    (ktcore.sigpred γ.(cfg.sigpredγ)) ∗
  "#Hown_vrf" ∷ cryptoffi.own_vrf_sk ptr_vrf γ.(cfg.vrf_pk) ∗
  "#Hsl_commit" ∷ sl_commit ↦*□ obj.(commit) ∗
  "%Hlen_commit" ∷ ⌜Z.of_nat (length obj.(commit)) = cryptoffi.hash_len⌝.

End proof.
End secrets.

Module keyStore.
Record t := mk' {
  plain : keys_ty;
}.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own_plain ptr_plain (plain : keys_ty) q : iProp Σ :=
  ∃ ptr0_plain,
  "Hptr_plain" ∷ map.own_map ptr_plain (DfracOwn q) ptr0_plain ∗
  "Hptr0_plain" ∷ [∗ map] uid ↦ sl_pks;pks ∈ ptr0_plain;plain,
    ∃ sl0_pks,
    "Hsl_pks" ∷ sl_pks ↦*{#q} sl0_pks ∗
    "Hcap_pks" ∷ own_slice_cap slice.t sl_pks (DfracOwn q) ∗
    "#Hsl0_pks" ∷ ([∗ list] sl_pk;pk ∈ sl0_pks;pks,
      "Hsl_pk" ∷ sl_pk ↦*□ pk).

Definition is_hidden γ commit_sec plain (hidden : gmap (list w8) (list w8)) : iProp Σ :=
  [∗ map] uid ↦ kt_pks ∈ plain,
    [∗ list] ver ↦ kt_pk ∈ kt_pks,
      ∃ label rand mapVal,
      "#His_MapLabel" ∷ ktcore.is_MapLabel γ.(cfg.vrf_pk) uid (W64 ver) label ∗
      "#His_CommitRand" ∷ ktcore.is_CommitRand commit_sec label rand ∗
      "#His_MapVal" ∷ ktcore.is_MapVal kt_pk rand mapVal ∗
      "%Hlook" ∷ ⌜hidden !! label = Some mapVal⌝.

Definition own ptr (obj : t) γ secs dig q : iProp Σ :=
  ∃ ptr_hidden hidden ptr_plain,
  "#Hstr_keyStore" ∷ ptr ↦□ (server.keyStore.mk ptr_hidden ptr_plain) ∗
  "Hown_hidden" ∷ merkle.own_Map ptr_hidden hidden dig (DfracOwn q) ∗
  "Hown_plain" ∷ own_plain ptr_plain obj.(plain) q ∗
  "#His_hidden" ∷ is_hidden γ secs.(secrets.commit) obj.(plain) hidden ∗
  "#His_dig" ∷ merkle.is_map hidden dig.

End proof.
End keyStore.

Module history.
Record t := mk' {
  digs: list (list w8);
}.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition is_audits γ digs audits : iProp Σ :=
  ∃ init_dig,
  "%Hlen_audits" ∷ ⌜length digs = length audits⌝ ∗
  "#His_upds" ∷ ([∗ list] ep ↦ aud ∈ audits,
    (* AuditProof is a transition to an epoch.
    for AuditProof @ ep0, need init_dig to transition from. *)
    ∃ dig0 dig1,
    "%Hlook0" ∷ ⌜(init_dig :: digs) !! ep = Some dig0⌝ ∗
    "%Hlook1" ∷ ⌜(init_dig :: digs) !! (S ep) = Some dig1⌝ ∗
    "#His_upd" ∷ ktcore.wish_ListUpdate dig0 aud.(ktcore.AuditProof.Updates) dig1) ∗
  "#His_sigs" ∷ ([∗ list] ep ↦ aud ∈ audits,
    ∃ link,
    "#His_link" ∷ hashchain.is_chain (take (S ep) digs) None link (S ep) ∗
    "#His_sig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk) (W64 ep) link
      aud.(ktcore.AuditProof.LinkSig)).

Definition own ptr (obj : t) γ q : iProp Σ :=
  ∃ ptr_chain sl_audits sl0_audits audits sl_vrfSig vrfSig,
  "Hstr_history" ∷ ptr ↦{#q} (server.history.mk ptr_chain sl_audits sl_vrfSig) ∗
  "Hown_chain" ∷ hashchain.own ptr_chain obj.(digs) (DfracOwn q) ∗

  "Hsl_audits" ∷ sl_audits ↦*{#q} sl0_audits ∗
  "Hcap_audits" ∷ own_slice_cap loc sl_audits (DfracOwn q) ∗
  "#Hown_audits" ∷ ([∗ list] idx ↦ p; aud ∈ sl0_audits; audits,
    ktcore.AuditProof.own p aud (□)) ∗
  "#His_audits" ∷ is_audits γ obj.(digs) audits ∗

  "#Hsl_vrfSig" ∷ sl_vrfSig ↦*□ vrfSig ∗
  "#His_vrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.sig_pk) γ.(cfg.vrf_pk) vrfSig.

End proof.
End history.

Module work.
Record t := mk' {
  Uid : w64;
  Ver : w64;
  Pk : list w8;
  Err : bool;
}.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj γ : iProp Σ :=
  ∃ sl_pk uidγ i,
  "Hstr_Work" ∷ ptr ↦ (server.Work.mk obj.(Uid) obj.(Ver) sl_pk obj.(Err)) ∗
  "#Hsl_pk" ∷ sl_pk ↦*□ obj.(Pk) ∗
  "%Hlook_uidγ" ∷ ⌜γ.(cfg.uidγ) !! obj.(Uid) = Some uidγ⌝ ∗
  "#Hput_perm" ∷ mono_list_idx_own uidγ i (obj.(Ver), obj.(Pk)).

Definition own_aux γ (ptr : loc) : iProp Σ := ∃ obj, own ptr obj γ.

End proof.
End work.

Module Server.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr γ σ q : iProp Σ :=
  ∃ ptr_secs secs ptr_keys keys ptr_hist hist ptr_workQ workQγ lastDig,
  "#Hfld_secs" ∷ ptr ↦s[server.Server::"secs"]□ ptr_secs ∗
  "#Hfld_keys" ∷ ptr ↦s[server.Server::"keys"]□ ptr_keys ∗
  "#Hfld_hist" ∷ ptr ↦s[server.Server::"hist"]□ ptr_hist ∗
  "#Hfld_workQ" ∷ ptr ↦s[server.Server::"workQ"]□ ptr_workQ ∗

  "#Hown_secs" ∷ secrets.own ptr_secs secs γ ∗
  "Hown_keys" ∷ keyStore.own ptr_keys keys γ secs lastDig q ∗
  "Hown_hist" ∷ history.own ptr_hist hist γ q ∗
  "#His_workQ" ∷ simple.is_simple workQγ ptr_workQ (work.own_aux γ) ∗

  "%Heq_hist" ∷ ⌜σ.(state.hist).*1 = hist.(history.digs)⌝ ∗
  "%Heq_last_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, keys.(keyStore.plain))⌝.

Definition lock_perm ptr γ : iProp Σ :=
  ∃ ptr_mu,
  "#Hfld_mu" ∷ ptr ↦s[server.Server::"mu"]□ ptr_mu ∗
  "Hperm" ∷ own_RWMutex ptr_mu (λ q, ∃ σ, own ptr γ σ q).

End proof.
End Server.

(** specs. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Lemma wp_Server_Put s γ uid sl_pk pk ver :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    (* caller doesn't need anything from Put.
    and in fact, Put might logically execute *after* Put returns. *)
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      let σ' := set state.pending (pure_put uid pk ver) σ in
      (own_Server γ σ' ={∅,⊤}=∗ True))
  }}}
  s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver
  {{{ RET #(); True }}}.
Proof. Admitted.

Lemma wp_Server_History s γ (uid prevEpoch prevVerLen : w64) Q :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      (own_Server γ σ ={∅,⊤}=∗ Q σ))
  }}}
  s @ (ptrT.id server.Server.id) @ "History" #uid #prevEpoch #prevVerLen
  {{{
    sl_chainProof sl_linkSig sl_hist ptr_bound err σ lastDig lastKeys,
    RET (#sl_chainProof, #sl_linkSig, #sl_hist, #ptr_bound, #err);
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "HQ" ∷ Q σ ∗
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗
    "#Herr" ∷
      match err with
      | true => ⌜uint.nat prevEpoch ≥ numEps ∨
        uint.nat prevVerLen > length pks⌝
      | false =>
        ∃ lastLink chainProof linkSig hist bound,
        "%Hnoof_eps" ∷ ⌜numEps = sint.nat (W64 $ numEps)⌝ ∗
        "%Hnoof_vers" ∷ ⌜length pks = sint.nat (W64 $ length pks)⌝ ∗
        "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗

        "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
        "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
        "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
        "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

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
      end
  }}}.
Proof. Admitted.

Lemma wp_Server_Audit s γ (prevEpoch : w64) Q :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      (own_Server γ σ ={∅,⊤}=∗ Q σ))
  }}}
  s @ (ptrT.id server.Server.id) @ "Audit" #prevEpoch
  {{{
    sl_proofs err σ, RET (#sl_proofs, #err);
    let numEps := length σ.(state.hist) in
    "HQ" ∷ Q σ ∗
    "Herr" ∷
      match err with
      | true => ⌜uint.nat prevEpoch ≥ numEps⌝
      | false =>
        (* we could explicitly tie down update labels and vals,
        but callers don't currently need that.
        this spec still gives the auditor same digs as server,
        and dig commits to exactly one map. *)
        ∃ proofs,
        "%Hnoof_eps" ∷ ⌜numEps = sint.nat (W64 $ numEps)⌝ ∗

        "#Hsl_proofs" ∷ ktcore.AuditProofSlice1D.own sl_proofs proofs (□) ∗
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
      end
  }}}.
Proof. Admitted.

Lemma wp_Server_Start s γ Q :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server s γ ∗
    "#Hfupd" ∷ □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
      (own_Server γ σ ={∅,⊤}=∗ Q σ))
  }}}
  s @ (ptrT.id server.Server.id) @ "Start" #()
  {{{
    ptr_chain chain ptr_vrf vrf σ last_link, RET (#ptr_chain, #ptr_vrf);
    let numEps := length σ.(state.hist) in
    "HQ" ∷ Q σ ∗
    "%Hnoof_eps" ∷ ⌜numEps = sint.nat (W64 $ numEps)⌝ ∗

    "#Hptr_chain" ∷ StartChain.own ptr_chain chain (□) ∗
    "#Hptr_vrf" ∷ StartVrf.own ptr_vrf vrf (□) ∗

    "%His_PrevEpochLen" ∷ ⌜uint.nat chain.(StartChain.PrevEpochLen) < numEps⌝ ∗
    "#His_PrevLink" ∷ hashchain.is_chain
      (take (uint.nat chain.(StartChain.PrevEpochLen)) σ.(state.hist).*1)
      None chain.(StartChain.PrevLink)
      (uint.nat chain.(StartChain.PrevEpochLen)) ∗
    "%His_ChainProof" ∷ ⌜hashchain.wish_Proof chain.(StartChain.ChainProof)
      (drop (uint.nat chain.(StartChain.PrevEpochLen)) σ.(state.hist).*1)⌝ ∗
    "#His_last_link" ∷ hashchain.is_chain σ.(state.hist).*1 None
      last_link numEps ∗
    "#His_LinkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
      (W64 $ numEps - 1) last_link chain.(StartChain.LinkSig) ∗

    "%Heq_VrfPk" ∷ ⌜γ.(cfg.vrf_pk) = vrf.(StartVrf.VrfPk)⌝ ∗
    "#His_VrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.sig_pk) γ.(cfg.vrf_pk)
      vrf.(StartVrf.VrfSig)
  }}}.
Proof. Admitted.

End proof.
End server.
