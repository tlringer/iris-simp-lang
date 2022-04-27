From iris.heap_lang Require Import proofmode notation.

Set Default Proof Using "Type".

(*
 * This example comes from Tej Chajed.
 * It is a version of or that short-circuits, so that
 * it is possible to write a simple proof.
 *)
Definition or: val :=
  λ: "x" "y", if: "x" then #true else "y".

Section heap.
  Context `{!heapGS Σ}.

  (*
   * This lemma proves that the short-circuit or
   * behaves like Coq's boolean orb on booleans.
   *)
  Lemma wp_or (x y: bool) :
    {{{ True }}}
      or #x #y
    {{{ (r:bool), RET #r; ⌜r = orb x y⌝ }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    unfold or.
    wp_pures.
    induction x; wp_pures.
    - iIntros "!>".
      iApply "HΦ". done.
    - iIntros "!>".
      iApply "HΦ". done.
  Qed.

End heap.

Print wp_or.