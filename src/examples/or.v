From iris_simp_lang Require Import simp.
From iris Require Import options.

Definition or: val :=  λ: "x" "y",
  if: "x" then #true else "y".

