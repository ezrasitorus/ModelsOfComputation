import tactic

inductive w_exp : Type
    | nat : ℕ → w_exp
    | add : w_exp → w_exp → w_exp
    -- | mul : w_exp → w_exp → w_exp
    -- | var : char → w_exp

inductive w_bool
    | true : w_bool
    | false : w_bool
    | equal : w_exp → w_exp → w_bool
    | not : w_bool → w_bool
    | and : w_bool → w_bool → w_bool
    | or : w_bool → w_bool → w_bool

inductive w_com : Type
    | assign : char → w_exp → w_com
    | if_then_else : w_bool → w_com → w_com
    | seq_comp : w_com → w_com → w_com
    | skip : w_com
    | while_do : w_bool → w_com → w_com

open w_exp

inductive b_eval : w_exp → ℕ → Prop
    | bnum : ∀ n : ℕ, b_eval (nat n) n
    | badd : ∀ E₁ E₂ : w_exp, ∀ n₁ n₂: ℕ, b_eval E₁ n₁ → b_eval E₂ n₂ → b_eval (add E₁ E₂) (n₂ + n₁)

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
    induction E with n E1 E2 ih1 ih2, -- Doing induction on E, the with part is naming the term used later
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
        specialize ih1 h1_n₁ h2_n₁ h1_a h2_a,
        specialize ih2 h1_n₂ h2_n₂ h1_a_1 h2_a_1,

        simp, -- simp simplifies the goal using definitions and other known stuff (maths). 
        -- Now the goal is about proving that adding some numbers give the same result
        linarith, -- linarith is used to prove stuff in arithmetic
    }
end

theorem b_step_totality : ∀ E : w_exp, ∃ n₁ : ℕ, b_eval E n₁ := 
begin
    -- This is a proof that big step evaluation is total
    intro E,
    induction E with m E1 E2 ih1 ih2,
    {
        use m,
        exact bnum m,
    },
    {
        rcases ih1 with ⟨m, hm⟩,
        rcases ih2 with ⟨n, hn⟩,
        use n + m,
        apply badd; assumption,
    }
end

def den : w_exp → ℕ 
    | (nat n) := n
    | (add E1 E2) := den E2 + den E1

theorem ps3_q3 : ∀ E : w_exp, ∀ n : ℕ, den E = n ↔ b_eval E n :=
begin
    intro E,
    induction E with m E1 E2 ih1 ih2,
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
            specialize ih1_mpr h_a,
            specialize ih2_mpr h_a_1,
            linarith,
        },
    },
end

inductive s_eval : w_exp → w_exp → Prop
    | s_left : ∀ E1 E2 E1' : w_exp, s_eval E1 E1' → s_eval (add E1 E2) (add E1' E2)
    | s_right : ∀ n : ℕ, ∀ E2 E2' : w_exp, s_eval E2 E2' → s_eval (add (nat n) E2) (add (nat n) E2')
    | s_num : ∀ p q r : ℕ, p + q = r →  s_eval (add (nat p) (nat q)) (nat r)

def normal_form (E : w_exp) : Prop := ∀ E' : w_exp, ¬ s_eval E E'

theorem s_step_determinacy : ∀ E E1 E2 : w_exp, s_eval E E1 → s_eval E E2 → E1 = E2 :=
begin
    -- This is a proof that small step evaluation is deterministic
    intro E,
    induction E with m E1 E2 ih1 ih2,
    {
        intros E1 E2 h,
        cases h,
    },
    {
        -- Inductive case - s_left
        intros E1' E2' h1 h2,
        cases h1,
        {
            cases h2,
            {
                -- This is the case that E1' and E2' are of the form E + E
                -- This can be easily dealt with using the inductive hypothesis on E1
                have help : h1_E1' = h2_E1',
                    exact ih1 _ _ h1_a h2_a,
                rw help,
            },
            -- The other cases are when E2' are n + E or n
            -- This means E1 is n and cannot be evaluated any further
            repeat {cases h1_a},
        },
        {
            -- This is the unductive case where E1' = n + E
            rename [h1_n n, h1_E2' F1, E2' F', E2 F],
            cases F',
            {
                -- This is the case when F' is a nat
                -- This cannot be possible : When does m + E → n? Only when E is a nat
                -- This means a nat reduces to F1, which is not possible
                cases h2,
                cases h1_a,
            },
            {
                -- This is the case when F' = E + E
                cases F'_a,
                {
                    -- This is the case when F'_a is a nat
                    -- Since we have a + in h2, this means that we got here from the s_left or s_right case
                        cases h2,
                    {
                        -- Here we prove it cannot be the s_left case
                        cases h2_a, -- A nat cannot be evaluated any further
                    },
                    {
                        -- We use the inductive hypothesis to prove the s_right case
                        specialize ih2 _ _ h1_a h2_a,
                        rw ih2,
                    }
                },
                {
                    -- This is the case when F'_a is E + E
                    -- This means a nat reduces to another expression, which is not possible
                    cases h2,
                    cases h2_a,
                }
            }
        },
        {
            -- This is the base case where E1' is a nat
            cases E2',
            {
                -- This is the case where E2' is also a nat
                cases h2,
                {
                    rw ← h1_a,
                    rw ← h2_a,
                },
            },
            {
                -- This is the case E2' is E + E
                cases h2;
                cases h2_a,
            },
        }
    }
end 
