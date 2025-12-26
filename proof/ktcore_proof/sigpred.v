From New.proof Require Import proof_prelude.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.proof.github_com.sanjit_bhat.pav Require Import
  hashchain merkle safemarshal.

From New.proof.github_com.sanjit_bhat.pav.ktcore_proof Require Import
  ktcore serde.

Module ktcore.
Import ktcore.ktcore serde.ktcore.

Module sigpred_cfg.
Record t :=
  mk {
    vrf: gname;
    startEp: gname;
    links: gname;
  }.
End sigpred_cfg.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition sigpred_vrf γ enc : iProp Σ :=
  ∃ vrfPk,
  "%Henc" ∷ ⌜enc = ktcore.VrfSig.pure_enc (ktcore.VrfSig.mk' (W8 ktcore.VrfSigTag) vrfPk)⌝ ∗
  "%Hvalid" ∷ ⌜safemarshal.Slice1D.valid vrfPk⌝ ∗

  "#Hshot" ∷ ghost_var γ (□) vrfPk.

Definition sigpred_links_inv links : iProp Σ :=
  ∃ digs cut maps,
  (* [offset] is the number of digs prior to links starting. *)
  let offset := (length digs - length links)%nat in
  "#Hlinks" ∷ ([∗ list] idx ↦ link ∈ links,
    let n_digs := (offset + idx + 1)%nat in
    "#His_link" ∷ hashchain.is_chain (take n_digs digs) cut link n_digs) ∗
  "%Hlt_links" ∷ ⌜length links ≤ length digs⌝ ∗
  "#Hmaps" ∷ ([∗ list] idx ↦ _;m ∈ links;maps,
    ∃ dig,
    "%Hlook_dig" ∷ ⌜digs !! (offset + idx)%nat = Some dig⌝ ∗
    "#His_map" ∷ merkle.is_map m dig) ∗
  "%Hmono" ∷ ⌜∀ i m0 m1,
    maps !! i = Some m0 →
    maps !! (S i) = Some m1 →
    m0 ⊆ m1⌝.

Definition sigpred_links γstartEp γlinks enc : iProp Σ :=
  (* [links] are all audited. they start from [startEp]. *)
  ∃ ep link startEp links,
  "%Henc" ∷ ⌜enc = ktcore.LinkSig.pure_enc (ktcore.LinkSig.mk' (W8 ktcore.LinkSigTag) ep link)⌝ ∗
  "%Hvalid" ∷ ⌜safemarshal.Slice1D.valid link⌝ ∗

  (* externalize startEp so that users agree on the epochs associated with links. *)
  "#Hshot" ∷ ghost_var γstartEp (□) startEp ∗
  "#Hlb" ∷ mono_list_lb_own γlinks links ∗
  "%Hlook" ∷ ⌜links !! (uint.nat ep - uint.nat startEp)%nat = Some link⌝ ∗
  "#Hinv" ∷ sigpred_links_inv links.

Definition sigpred γ enc : iProp Σ :=
  sigpred_vrf γ.(sigpred_cfg.vrf) enc ∨ sigpred_links γ.(sigpred_cfg.startEp) γ.(sigpred_cfg.links) enc.

#[global] Instance sigpred_pers γ e : Persistent (sigpred γ e).
Proof. apply _. Qed.

End proof.
End ktcore.
