def n : ℕ := 10

@[instance] def cong_rel : setoid ℕ :=
{ r     := λ(x y : ℕ), x % n = y % n,
  iseqv :=
    begin
      rw equivalence,
      repeat { apply and.intro }, {
        rw reflexive,
        intro x,
        refl,
      }, {
        rw symmetric,
        intros x y,
        intro hxy,
        rw hxy,
      }, {
        rw transitive,
        intros x y z,
        intros hxy hyz,
        rw [hxy, hyz],
      },
    end }

lemma ℕₙ.rel_iff (x y : ℕ) :
  x ≈ y ↔
  x % n = y % n :=
by refl

/- Define ℤ/nℤ or ℤ_n aka ℕₙ from the congruence relation on ℕ. -/
def ℕₙ : Type :=
  quotient cong_rel

def ℕₙ.add : ℕₙ → ℕₙ → ℕₙ :=
  quotient.lift₂ (λ(x y : ℕ), ⟦x + y % n⟧) begin
      intros x y x' y' hx hy,
      apply quotient.sound,
      rw ℕₙ.rel_iff at *,
      norm_num,
      rw nat.add_mod,
      rw [hx, hy],
      rw ←nat.add_mod,
    end

def ℕₙ.sub : ℕₙ → ℕₙ → ℕₙ :=
  quotient.lift₂ (λ(x y : ℕ), ⟦(x + (n - (y % n)) % n)⟧) begin
      intros x y x' y' hx hy,
      apply quotient.sound,
      rw ℕₙ.rel_iff at *,
      norm_num,
      rw nat.add_mod,
      rw [hx, hy],
      rw ←nat.add_mod,
    end

def ℕₙ.le : ℕₙ → ℕₙ → Prop :=
  quotient.lift₂ (λ(x y : ℕ), (x % n) ≤ (y % n)) begin
      intros x y x' y' hx hy,
      rw ℕₙ.rel_iff at *,
      norm_num,
      apply iff.intro, {
        rw [hx, hy],
        intro h,
        assumption,
      }, {
        intro h,
        rw [hx, hy],
        assumption,
      },
    end

def ℕₙ.ge (a b : ℕₙ) : Prop := ℕₙ.le b a

@[instance] def ℕₙ.has_add : has_add ℕₙ := { add := ℕₙ.add }

@[instance] def ℕₙ.has_sub : has_sub ℕₙ := { sub := ℕₙ.sub }

@[instance] def ℕₙ.has_le : has_le ℕₙ := { le := ℕₙ.le }

-- @[instance] def ℕₙ.has_ge : has_ge ℕₙ := { ge := ℕₙ.ge }

@[instance] def ℕₙ.has_zero : has_zero ℕₙ := { zero := ⟦0⟧ }

@[instance] def ℕₙ.has_one : has_one ℕₙ := { one := ⟦1⟧ }

def add_mod : ℕₙ → ℕₙ → ℕₙ:=
  quotient.lift₂ (λ(x y : ℕₙ), ⟦x⟧) begin