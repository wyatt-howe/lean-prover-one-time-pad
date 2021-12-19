import data.real.cardinality

/-! # CSCI 1951-X Final Project
    # Wyatt Howe

Proving basic properties of crypto schemes. -/

set_option pp.beta true
set_option pp.generalized_field_notation false
open_locale cardinal

namespace project


/-! # Type system vs mathlib

The following would be trivial to prove for in ℤ, and were easily implemented
  when I originally was using a quotient type ℤ/nℤ modeling an additive group,
  but for the natural numbers they become slightly less intuitive. -/

lemma nat_sub_add_cancel : ∀(a b : ℕ), b ≤ a → a = (a - b) + b
| a b hab := ((nat.sub_eq_iff_eq_add hab).mp rfl)

lemma nat_add_sub_assoc :
  ∀(a b c : ℕ),
    b > c →
      (a + b) - c = a + (b - c)
  :=
λ(a b c hlt), nat.add_sub_assoc (le_of_lt hlt) a

lemma nat_mod_add_cancel :
  ∀(a b c n : ℕ),
    (a + c) % n = (b + c) % n
      ↔ a % n = b % n
  :=
by sorry,

/-! Use of the tactic `simp` hides a lot of the arithmetic rules that had
initially implemented for ℕₙ (see other file).  There came a point where I
decided to switch to plain ℕ becasue my proof of `perfect_secrecy` was 300+
lines, and I still had several sorried-out sub-proofs of statements that were
obvious to me, but tedious to prove without the help of the standard library.

Switching to ℕ and the build-in tactics was not without problems of its own.
I had to resort to hacky ways to inject a second implication for an upper-
bound in the `≤` induction mini-proofs.  For example, `A→B` became `¬A∨B` in
some places. -/

/-helper-/
lemma or_resolve_left (A B : Prop) : (A ∨ B) → (¬A) → B :=
begin
  intros hn hor,
  exact or.resolve_left hn hor,
end


/-! ## Part I: Perfect secrecy.

The [one-time pad](https://en.wikipedia.org/wiki/One-time_pad#Perfect_secrecy)
is an encryption scheme that utilizes a random mask as the encryption key to
guarantee that nothing about the plaintext message is revealed (but its length).


-/

namespace one_time_pad

/-! The group modulus is `q`.  I have set `q` to ten to
make later #reduce statements concise, but perfect secrecy
is not dependent on the size of `q` its proof will hold even
when `num % q` is too large to be practically computible,
(so long as there is a proof it is not 0). -/

def q : ℕ := 10

lemma hqneqzero : q ≠ 0 := dec_trivial

/-! Encryption is simply modular addition. -/
def enc : ℕ → ℕ → ℕ
| k m := (m + k) % q

/-! Encryption is simply modular subtraction. -/
def dec : ℕ → ℕ → ℕ
| k c := (c - k) % q

/-! Check if c is a valid ciphertext. -/
def is_ct : ℕ → Prop
| c := c < q

/-! Check if m is a valid plaintext. -/
def is_pt : ℕ → Prop
| m := m < q

/-lemma invertible_enc : ∀(k m : ℕ), dec k (enc k m) = m := begin
    intros k m,
    rw [enc, dec],
    sorry,
  end-/

/-lemma invertible_dec : ∀(k c : ℕ), enc k (dec k c) = c := begin
    intros k c,
    rw [dec, enc],
    sorry,
  end-/

/-! Each encryption of a message has a unique key with respect to its ciphertext. -/
lemma uniqueness_of_keys : ∀(k₁ < q), ∀(k₂ < q), ∀m, (enc k₁ m = enc k₂ m) → (k₁ = k₂) := begin
  intros k₁ hk₁ k₂ hk₂ m,
  rw [enc, enc],
  intro hkeq,
  have mod_reduce : ∀(k < q), k % q = k := λk, nat.mod_eq_of_lt,
  rewrite [
    nat.add_comm, eq_comm, nat.add_comm, eq_comm,
    nat_mod_add_cancel, mod_reduce k₁, mod_reduce k₂
  ] at hkeq,
  repeat { assumption },
end

lemma uniqueness_of_keys' : ∀(k₁ < q), ∀(k₂ < q), ∀m, k₁ ≠ k₂ → enc k₁ m ≠ enc k₂ m := begin
  intros k₁ hk₁ k₂ hk₂ m,
  contrapose,
  intro hkeq,
  simp, simp at hkeq,
  apply uniqueness_of_keys k₁ hk₁ k₂ hk₂,
  assumption,
end

/-! # Probabilites

As discussed in more clarity in the appendix, probabilities are
modeled by the sum over a domain, here `[0, q)`, where `q` is a
non-zero natural number.  This sum is then normalized by dividing
by the size of such domain.  In the proof, we perform induction
over this probability counting function in three parts:

  (1)  from 0 to k
  (2)  at k itself
  (3)  onward from k until q

where `k` is where an event happens.  There is only one ``event''
in the one-time pad -- when a ciphertext-plaintext pair decrypts
correctly.  If two plaintext messages encrypt to / decrypt from
the same ciphertext with equal probability (trivially, 1/q), then
we say the overall scheme has _perfect secrecy_.  See below. -/

def Pr_bounded : ℕ → (ℕ → bool) → ℕ
| 0 f     := 0
| (l+1) f := Pr_bounded l f + if f l then 1 else 0

def Pr_count : (ℕ → bool) → ℕ :=
  λf, Pr_bounded q f

def Pr : (ℕ → bool) → ℚ :=
  λf, ↑(Pr_count f) / ↑q

#eval Pr(λk, (enc k 4 = 5))

lemma perfect_secrecy :
  ∀(m₁ m₂ : ℕ), is_pt m₁ → is_pt m₂ →
  ∀(c : ℕ), is_ct c →
      Pr(λk, enc k m₁ = c)
    = Pr(λk, enc k m₂ = c)
  :=
begin
  intros m₁ m₂ m₁_is_pt m₂_is_pt,
  intros c c_is_ct,

  rw Pr,

  have hPr1 : ∀mᵢ, is_pt mᵢ → Pr_count(λk, (enc k mᵢ = c)) = 1 := begin
    rw Pr_count,
    intro mᵢ,

    intro mᵢ_is_pt,
    
    have pt_is_lt_q : ∀m, is_pt m → m < q := λm, gt.lt,
    have hmᵢltq : mᵢ < q := pt_is_lt_q mᵢ mᵢ_is_pt,
    
    have ct_is_lt_q : ∀m, is_ct m → m < q := λm, gt.lt,
    have hcltq : c < q := ct_is_lt_q c c_is_ct,

    let kᵢ := (c + q - mᵢ) % q,
    have hkᵢ : kᵢ = (c + q - mᵢ) % q := rfl,

    have hqgtzero : q > 0 := zero_lt_iff.mpr hqneqzero,
    have hkᵢltq : kᵢ < q := begin
      rw hkᵢ,
      apply nat.mod_lt,
      exact hqgtzero,
    end,

    have hc : c = enc kᵢ mᵢ := begin
      have henc : enc kᵢ mᵢ = c := 
        calc
          enc kᵢ mᵢ = (mᵢ + kᵢ) % q :
            begin
              rw enc,
            end
          ... = (mᵢ + (c + q - mᵢ)) % q :
            begin
              rw hkᵢ,
              simp,
            end
          ... = ((c + q - mᵢ) + mᵢ) % q :
            begin
              rw nat.add_comm,
            end
          ... = (c + (q - mᵢ) + mᵢ) % q :
            begin
              rw nat_add_sub_assoc,
              exact hmᵢltq,
            end
          ... = (c + (q - mᵢ + mᵢ)) % q :
            begin
              rw [add_assoc c (q - mᵢ) mᵢ],
            end
          ... = (c + q) % q :
            begin
              have hcancelmᵢ : (q - mᵢ) + mᵢ = q := begin
                apply eq.symm,
                apply nat_sub_add_cancel,
                apply le_of_lt,
                exact hmᵢltq,
              end,
              rw [hcancelmᵢ],
            end
          ... = c % q :
            begin
              simp,
            end
          ... = c :
            begin
              exact nat.mod_eq_of_lt hcltq,
            end
      ,
      rw ←henc,
    end,

    have h : ∀(z : ℕ), z > kᵢ → (¬(z ≤ q) ∨ Pr_bounded z (λk, enc k mᵢ = c) = 1) := begin
      apply nat.le_induction, {
        apply or.intro_right,

        /- Compute up to kᵢ from nat.zero. -/

        rw Pr_bounded, simp, rw ←hc, simp,
        
        have hltkᵢ : ∀k' < kᵢ, Pr_bounded k' (λk, enc k mᵢ = c) = 0 := begin
          intros k' hltk',
          induction k' with k' ih, {
            rw Pr_bounded,
          }, {
            rw Pr_bounded,
            simp,
            apply and.intro, {
              apply ih,
              apply nat.lt_of_succ_lt,
              exact hltk',
            }, {
              have hk'ltq : k' < q := nat.lt_of_succ_lt (lt_trans hltk' hkᵢltq),
              have hk'neqkᵢ : enc k' mᵢ ≠ c := begin
                rw hc,
                apply uniqueness_of_keys',  -- If the encryptions were the same, their keys would be same.
                assumption, assumption,
                apply ne_of_lt,
                apply nat.lt_of_succ_lt,
                exact hltk',
              end,
              contradiction,
            },
          },
        end,

        have hem : ((kᵢ=0) ∨ ¬(kᵢ=0)) → Pr_bounded kᵢ (λk, enc k mᵢ = c) = 0 := begin
          intro ht,
          cases ht, {
            rw [ht, Pr_bounded],
          }, { 
            let kpred := kᵢ-1,
            have hkpred : kpred+1 = kᵢ := begin
              have hpos : kᵢ > 0 := zero_lt_iff.mpr ht,

              have hdef : kpred = kᵢ-1 := rfl,
              rw hdef,
              apply eq.symm,
              apply nat_sub_add_cancel,
              exact nat.succ_le_iff.mpr hpos,
            end,

            /- Compute the count at kᵢ given then sum from 0 to kᵢ-1. -/

            rw [←hkpred, Pr_bounded],
            simp,
            apply and.intro, {
              apply hltkᵢ,
              rw ←hkpred,
              exact lt_add_one kpred,
            }, {
              have hk'neqkᵢ : enc kpred mᵢ ≠ c := begin
                have hneq : kpred ≠ kᵢ := begin
                  have lhkpred : kᵢ = kpred+1 := eq.symm hkpred,
                  rw lhkpred,
                  linarith,
                end,
                rw hc,
                have hkpredltkᵢ : kpred < kᵢ := nat.succ_le_iff.mp (eq.ge (eq.symm hkpred)),
                have hkpredltq : kpred < q := lt_trans hkpredltkᵢ hkᵢltq,
                apply uniqueness_of_keys',  -- If the encryptions were the same, their keys would be same.
                assumption, assumption,
                assumption,
              end,
              contradiction,
            },
          },
        end,
        
        apply hem,
        exact em (kᵢ = 0),
      }, {
        intros q' hgteqq' ih,

        /- Compute from kᵢ to q exclusively. -/

        have hem : ((q'<q) ∨ ¬(q'<q)) → (
          ¬(q' < q) ∨ (
            Pr_bounded (q' + 1) (λk, enc k mᵢ = c) = 1
          )
        ) := begin
          intro ht,
          cases ht, {
            apply or.intro_right,
            have hq' : kᵢ < q' := nat.succ_le_iff.mp hgteqq',
            have hq'neqkᵢ : enc q' mᵢ ≠ c := begin
              rw hc,
              have hq'ltq : q' < q := ht,
              apply uniqueness_of_keys',  -- If the encryptions were the same, their keys would be same.
              assumption, assumption,
              exact ne_of_gt hq',
            end,
            rw Pr_bounded,
            simp,
            have ihh : Pr_bounded q' (λk, enc k mᵢ = c) = 1 := begin
              apply or_resolve_left ¬(q' ≤ q), {
                assumption,
              }, {
                simp,
                exact le_of_lt ht,
              },
            end,
            rw [ihh],
            split_ifs, {
              contradiction,  -- (h ∧ hq'neqkᵢ) → false
            }, {
              refl,
            },
          }, {
            apply or.intro_left,
            assumption,
          },
        end,
        apply hem,
        exact em (q' < q),
      },
    end,

    have upper_bound_q :
      ¬(q ≤ q) ∨ Pr_bounded q (λk, enc k mᵢ = c) = 1
               → Pr_bounded q (λk, enc k mᵢ = c) = 1
      :=
    begin
      intro,
      apply or_resolve_left ¬(q ≤ q), {
        assumption,
      }, {
        simp,
      },
    end,
    apply upper_bound_q,

    exact h q hkᵢltq,
  end,

  have hPrm₁_count : Pr_count (λk, enc k m₁ = c) = 1 := hPr1 m₁ m₁_is_pt,
  have hPrm₂_count : Pr_count (λk, enc k m₂ = c) = 1 := hPr1 m₂ m₂_is_pt,

  simp [hPrm₁_count, hPrm₂_count],
end

/-! Let's test it out! -/
def c := 6
def c_is_ct : is_ct 6 := sorry
def m₁ := 5
def m₂ := 4
def m₁_is_pt : is_pt 5 := sorry
def m₂_is_pt : is_pt 4 := sorry

#check perfect_secrecy m₁ m₂ m₁_is_pt m₂_is_pt c c_is_ct

/-! Results:

You should see that for the ciphertext 6, the plaintext message was
equally likely to be 5 as it is to be 4, thus we learn nothing.

Formally, we write this as Pr[enc(k, m₁) = c] = Pr[enc(k, m₂) = c].

Notice how without the key, an attacker cannot determine with even
a fractionally higher probility which messages to favor over others,
and so guessing is useless.  We have acheived perfect secrecy. -/

end one_time_pad


/-! # Part II: Hardness assumptions

As it turns out, the more `advanced' cryptosystems are trivial to
prove when their security depends directly on a reduction to another
hard problem.  If you can break the scheme, you can also solve this
hard problem, and no one has ever solved that hard problem before...

I give an example, but you can see how there is not much to prove
beyond the same boilerplate reduction to a known hard problem.

The design of some other schemes is that they are provably secure
in the ``random oracle model'', meaning their security depends on
the existence of a oracle that takes produces random data and is
prefectly unpredictable - not unlike how the one-time pad derives
its security from the randomness of the key.-/

namespace goldwasser_micali

/-! Ref: https://en.wikipedia.org/wiki/Goldwasser%E2%80%93Micali_cryptosystem#Security_properties -/

def publicKey : Type := ℕ × ℕ
def ciphertext : Type := ℕ
def plaintext : Type := bool

def rand : unit → ℕ := sorry,

def to_pt : ℕ → plaintext := sorry

def encrypt : publicKey → plaintext → ciphertext := sorry,

/-!
  It is impossible to decrypt a GM ciphertext without knowing whether it is a
  quadratic residue, but determining this requires knowledge of the factorization
  of the public key, _i.e._ the secret key, thus breaking the security guarantee.
-/
def decrypt_without_secret_key : publicKey → ciphertext → plaintext := sorry,

/-!
  If we can successfully decrypt, then `x` in the public key must be a non-residue.
  Else, we succeed with a 50/50 chance. After a small number of tries it would be
  possible to say with a high confidence whether or not `x` is a quadratic residue.
-/
def reduction : (publicKey → ciphertext → plaintext) → ℕ → bool
| decrypt x := (
  (λ(p q: ℕ),
    (λ(N: ℕ),
      (λ(pk: publicKey),
        to_bool (
          decrypt pk (encrypt pk (to_pt x)) = (to_pt x)
        )
      ) (x, N)
    ) (p * q)
  ) (rand ()) (rand ())
)

def is_quadratic_residue_mod_N : ℕ → bool := reduction decrypt_without_secret_key

end goldwasser_micali



/-! # Appendix: More counting functions. -/
namespace counting

/-!
While the overall structure of the perfect secrecy proof is
quite basic, its execution is in practice somewhat tedious.

A possibe next step could be to meta-program a tactic which
evaluates these recursive sums of `point functions' (functions
that are 1 at one point and 0 everywhere else) by handling the
desired upper and lower bounds for the inductionive sub-proofs.

Small examples can be proved reflexively:
-/

def f : ℕ → ℕ
| 0     := 0
| (l+1) := f l + if l+1=5 then 1 else 0

#reduce f 10
#reduce f 6
#reduce f 5
#reduce f 4
#reduce f 1

lemma hf : ∀k, k≥5 → f k = 1 := begin
  intro k,

  apply nat.le_induction, {
    ring,
  }, {
    intros q hnlt5 hfn,
    rw [f],
    split_ifs, {
      linarith,
    }, {
      assumption,
    },
  },
end

/-! A more advanced example where the point is variable: -/

def a : ℕ := 5555

def F : ℕ → ℕ → ℕ
| 0 a     := if 0=a then 1 else 0
| (l+1) a := F l a + if l+1=a then 1 else 0

lemma hF : ∀a, ∀k, k≥a → F k a = 1 := begin
  intros a k,
  apply nat.le_induction, {
    cases a, {
      refl,
    }, {
      rw [F],
      simp,
      have hh : ∀i, i ≤ a → F i a.succ = 0 := begin
        intro i,
        induction i, {
          simp,
          refl,
        }, {
          rename i_ih ih,
          rename i_n i,
          intro hilteqa,
          have hilta : i < a := hilteqa,
          rw [F],
          simp,
          apply and.intro, {
            apply ih,
            exact le_of_lt hilta,
          }, {
            intro h,
            have hi1eqa1 : i+1 = a+1 := by rw [h],
            have hieqa : i = a := by linarith,
            linarith,
          },
        },
      end,
      apply hh,
      apply eq.ge,
      refl,
    },
  }, {
    intros k hklteq5 ih,
    rw [F],
    split_ifs, {
      linarith,
    }, {
      assumption,
    },
  },
end

/-! When the point condition a function of multiple variables, you
      get a proof like I wrote to prove perfect secrecy of the OTP. -/

end counting

end project
