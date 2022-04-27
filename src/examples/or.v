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

  Lemma wp_short_circuit_or (x y: bool) :
    {{{ True }}}
      or #x #y
    {{{ (r:bool), RET #r; ⌜r = orb x y⌝ }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    rewrite /or.
    wp_pures.
    destruct x; wp_pures.
    - iIntros "!>".
      iApply "HΦ". done.
    - iIntros "!>".
      iApply "HΦ". done.
  Qed.

End heap.