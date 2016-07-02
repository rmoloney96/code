Require Import ZArith.
Open Local Scope Z_scope.

Inductive fact_domain : Z -> Prop :=
| fact_domain_zero :
  fact_domain 0
| fact_domain_pos :
  forall z : Z, z >= 0 -> fact_domain (Zminus z 1) -> fact_domain z.

Theorem fact_domain_pos_true : forall z : Z, fact_domain z -> z >= 0.
intros x H.
case H.
unfold Zge.
discriminate.
intros.
assumption.
Defined.

Theorem fact_domain_inv :
  forall z : Z, fact_domain z -> z > 0 -> fact_domain (Zminus z 1).
intros z H.
case H.
intros.
discriminate.
intros.
assumption.
Defined.

Fixpoint fact (z : Z) (h : fact_domain z) {struct h} : Z :=
match Z_gt_le_dec z 0 with
  | right hle =>
    match Z_ge_lt_dec z 0 with
      | right hlt => False_rec Z (fact_domain_pos_true z h hlt)
      | left _ => 1
    end
  | left hgt =>
    z * (fact (Zminus z 1) (fact_domain_inv z h hgt))
end.