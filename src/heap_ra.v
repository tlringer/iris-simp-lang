From iris.algebra Require Import gmap_view frac.
From iris.algebra Require Export dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
Import uPred.

(** This file provides a generic mechanism for a language-level point-to
connective [l ↦{dq} v] reflecting the physical heap.  This library is designed to
be used as a singleton (i.e., with only a single instance existing in any
proof), with the [gen_heapG] typeclass providing the ghost names of that unique
instance.  That way, [mapsto] does not need an explicit [gname] parameter.
This mechanism is plugged into a language and related to the physical heap
by using [gen_heap_interp σ] in the state interpretation of the weakest
precondition. See primitive_laws.v for where that happens.
 *)

(** The CMRAs we need, and the global ghost names we are using. *)

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_preG_inG :> inG Σ (gmap_viewR L (leibnizO V));
}.

Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapG {
  gen_heap_inG :> gen_heapPreG L V Σ;
  gen_heap_name : gname;
}.
Global Arguments GenHeapG L V Σ {_ _ _} _ : assert.
Global Arguments gen_heap_name {L V Σ _ _} _ : assert.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (gmap_viewR L (leibnizO V))
].

Global Instance subG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapG L V Σ}.

  Definition gen_heap_interp (σ : gmap L V) : iProp Σ :=
    own (gen_heap_name hG) (gmap_view_auth 1 (σ : gmap L (leibnizO V))).

  Definition mapsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    own (gen_heap_name hG) (gmap_view_frag l dq (v : leibnizO V)).
  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapG L V Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (Φ : V → iProp Σ).
  Implicit Types (σ : gmap L V) (l : L) (v : V).

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l dq v : Timeless (l ↦{dq} v).
  Proof. rewrite mapsto_eq. apply _. Qed.
  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
  Proof.
    intros p q. rewrite mapsto_eq /mapsto_def -own_op gmap_view_frag_add //.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝%Qp.
  Proof.
    rewrite mapsto_eq. iIntros "Hl".
    iDestruct (own_valid with "Hl") as %?%gmap_view_frag_valid. done.
  Qed.
  Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite mapsto_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_view_frag_op_valid_L.
    auto.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (mapsto_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  Lemma mapsto_combine l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapsto_agree with "Hl1 Hl2") as %->.
    iCombine "Hl1 Hl2" as "Hl".
    rewrite mapsto_eq /mapsto_def -own_op gmap_view_frag_op.
    auto.
  Qed.

  Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    iIntros (?) "Hl1 Hl2"; iIntros (->).
    by iDestruct (mapsto_valid_2 with "Hl1 Hl2") as %[??].
  Qed.
  Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. apply mapsto_frac_ne. intros ?%exclusive_l; [done|apply _]. Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (gmap_view_alloc _ l (DfracOwn 1)); done. }
    iModIntro. iFrame.
  Qed.

  Lemma gen_heap_valid σ l dq v : gen_heap_interp σ -∗ l ↦{dq} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq.
    by iDestruct (own_valid_2 with "Hσ Hl") as %[??]%gmap_view_both_valid_L.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl") as %[_ Hl]%gmap_view_both_valid_L.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply gmap_view_update. }
    iModIntro. iFrame.
  Qed.
End gen_heap.

Lemma gen_heap_init `{Countable L, !gen_heapPreG L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapG L V Σ,
    gen_heap_interp σ.
Proof.
  iMod (own_alloc (gmap_view_auth 1 (σ : gmap L (leibnizO V)))) as (γ) "Hσ".
  { exact: gmap_view_auth_valid.  }
  iExists (GenHeapG _ _ _ γ).
  done.
Qed.
