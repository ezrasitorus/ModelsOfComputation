import while

open w_exp

inductive b_eval : w_exp → ℕ → Prop
    | bnum : ∀ n : ℕ, b_eval (nat n) n
    | badd : ∀ E₁ E₂ : w_exp, ∀ n₁ n₂: ℕ, b_eval E₁ n₁ → b_eval E₂ n₂ → b_eval (add E₁ E₂) (n₂ + n₁)
    | bmul : ∀ E₁ E₂ : w_exp, ∀ n₁ n₂: ℕ, b_eval E₁ n₁ → b_eval E₂ n₂ → b_eval (mul E₁ E₂) (n₁ * n₂)

open b_eval

theorem lecture_2_easy : b_eval (add (nat 3) (add (nat 1) (nat 2))) 6 :=
begin
    apply badd,
    {
        apply bnum,
    },
    {
        apply badd (nat 1) (nat 2) 1 2,
        {
            exact bnum 1,
        },
        {
            exact bnum 2,
        }
    }
end

lemma bnum_trivial : ∀ m n : ℕ, b_eval (nat m) n ↔ m = n :=
begin
    intros m n,
    split,
    {
        intro h,
        cases h,
        refl,
    },
    {
        intro h,
        rw h,
        apply bnum,
    }
end

theorem b_step_determinacy : ∀ E : w_exp, ∀ n₁ n₂ : ℕ, b_eval E n₁ → b_eval E n₂ → n₁ = n₂ := 
begin
    -- This is a proof that big step evaluation is deterministic
    intro E, -- Introduces a term E : w_exp
    induction E with n E1 E2 ih1 ih2 E1 E2 ih1 ih2, -- Doing induction on E, the with part is naming the term used later
    {
        -- This is the base case. E = n.
        intros n1 n2 h1 h2, -- Introduces n1 n2 : ℕ and assumes b_eval n n1 and b_eval n n2. 
        -- These proofs are a type, and h1 and h2 are terms of this type
        cases h1, -- Doing a case analysis on h1, this changes n1 to n
        cases h2, -- Doing a case analysis on h2, this changes n2 to n
        refl, -- The goal is now n = n, which can be proved using the refl tactic
    },
    {
        -- This is the inductive case. We have E1 and E2 the proposition is true for them.
        -- We want to prove for E1 + E2
        intros m n h1 h2, -- Introduces n1 n2 : ℕ h1 h2 as before
        -- Case analysis on h1. This is like saying h1 can only be obtained using badd, so what
        -- other proofs can we infer. This is that m must be of the form a + b, for some naturals a b.
        -- We also get a proof of b_eval E1 a and b_eval E2 b. The same is done for h2.
        cases h1, 
        cases h2,

        -- We specialise our inductive hypotheses with the proofs we obtained above
        specialize ih1 h1_n₁ h2_n₁ h1_ᾰ h2_ᾰ,
        specialize ih2 h1_n₂ h2_n₂ h1_ᾰ_1 h2_ᾰ_1,

        simp, -- simp simplifies the goal using definitions and other known stuff (maths). 
        -- Now the goal is about proving that adding some numbers give the same result
        linarith, -- linarith is used to prove stuff in arithmetic
    },
    {
        intros m n h1 h2, -- Introduces n1 n2 : ℕ h1 h2 as before
        cases h1, 
        cases h2,

        -- We specialise our inductive hypotheses with the proofs we obtained above
        specialize ih1 h1_n₁ h2_n₁ h1_ᾰ h2_ᾰ,
        specialize ih2 h1_n₂ h2_n₂ h1_ᾰ_1 h2_ᾰ_1,

        simp [ih1, ih2],
    }
end

theorem b_step_totality : ∀ E : w_exp, ∃ n₁ : ℕ, b_eval E n₁ := 
begin
    -- This is a proof that big step evaluation is total
    intro E,
    induction E with m E1 E2 ih1 ih2 E1 E2 ih1 ih2,
    {
        use m,
        exact bnum m,
    },
    {
        rcases ih1 with ⟨m, hm⟩,
        rcases ih2 with ⟨n, hn⟩,
        use n + m,
        apply badd; assumption,
    },
    {
        rcases ih1 with ⟨m, hm⟩,
        rcases ih2 with ⟨n, hn⟩,
        use m * n,
        apply bmul; assumption,
    }
end

def den : w_exp → ℕ 
    | (nat n) := n
    | (add E1 E2) := den E2 + den E1
    | (mul E1 E2) := den E1 * den E2

theorem ps3_q3 : ∀ E : w_exp, ∀ n : ℕ, den E = n ↔ b_eval E n :=
begin
    intro E,
    induction E with m E1 E2 ih1 ih2 E1 E2 ih1 ih2,
    {
        intro n,
        split,
        {
            intro h,
            cases h,
            apply bnum,
        },
        {
            intro h,
            cases h,
            rw den,
        }
    },
    {
        intro n,
        split,
        {
            intro h,
            cases h,
            specialize ih1 (den E1),
            specialize ih2 (den E2),
            apply badd,
            {
                exact ih1.1 (rfl),
            },
            {
                exact ih2.1 (rfl),
            }
        },
        {
            intro h,
            cases h,
            specialize ih1 h_n₁,
            specialize ih2 h_n₂,
            simp, rw den,
            cases ih1, cases ih2,
            specialize ih1_mpr h_ᾰ,
            specialize ih2_mpr h_ᾰ_1,
            linarith,
        },
    },
    {
      intro n,
      split,
      {
        intro h,
        cases h,
        specialize ih1 (den E1),
        specialize ih2 (den E2),
        have h1 : b_eval E1 (den E1) := ih1.1 (rfl),
        have h2 : b_eval E2 (den E2) := ih2.1 (rfl),
        exact bmul _ _ _ _ h1 h2,
      },
      {
        intro h,
        cases h,
        specialize ih1 h_n₁,
        specialize ih2 h_n₂,
        simp, rw den,
        cases ih1, cases ih2,
        specialize ih1_mpr h_ᾰ,
        specialize ih2_mpr h_ᾰ_1,
        simp [ih1_mpr, ih2_mpr],
      }
    }
end