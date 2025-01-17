import Smt

theorem euf {U : Type} [Nonempty U] {f : U → U → U} {a b c d : U} : (a = b) → (c = d) → p1 ∧ True → (¬ p1) ∨ (p2 ∧ p3) → (¬ p3) ∨ (¬ (f a c = f b d)) → False := by
  smt
  exact (and_true p1).symm
