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
    | while_do : w_bool → w_com

open w_exp

inductive b_eval : w_exp → ℕ → Prop
    | bnum : ∀ n : ℕ, b_eval (nat n) n
    | badd : ∀ E₁ E₂ : w_exp, ∀ n₁ n₂: ℕ, b_eval E₁ n₁ → b_eval E₂ n₂ → b_eval (add E₁ E₂) (n₁ + n₂)

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
    intro E,
    induction E with n E1 E2 ih1 ih2,
    {
        intros n1 n2 h1 h2,
        cases h1,
        cases h2,
        refl,
    },
    {
        intros m n h1 h2,
        cases h1,
        cases h2,
        specialize ih1 h1_n₁ h2_n₁ h1_a h2_a,
        specialize ih2 h1_n₂ h2_n₂ h1_a_1 h2_a_1,
        simp, linarith,
    }
end

theorem b_step_totality : ∀ E : w_exp, ∃ n₁ : ℕ, b_eval E n₁ := 
begin
    intro E,
    induction E with m E1 E2 ih1 ih2,
    {
        use m,
        exact bnum m,
    },
    {
        rcases ih1 with ⟨m, hm⟩,
        rcases ih2 with ⟨n, hn⟩,
        use m + n,
        exact badd E1 E2 m n hm hn,
    }
end

def den : w_exp → ℕ 
    | (nat n) := n
    | (add E1 E2) := den E1 + den E2

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
    intro E,
    induction E with m E1 E2 ih1 ih2,
    {
        intros E1 E2,
        intro h,
        cases h,
    },
    {
        intros E1' E2' h1 h2,
        cases h1,
        {
            cases h2,
            {
                have help : h1_E1' = h2_E1',
                    exact ih1 _ _ h1_a h2_a,
                simp [help],
            },
            repeat {cases h1_a},
        },
        {
            rename [h1_n n, h1_E2' F1, E2' F', E2 F],
            cases F',
            {
                -- This is the case when F' is a nat
                -- This cannot be possible : since when did m + E → n?
                -- This means E is a nat as well
                cases h2,
                cases h1_a,
            },
            {
                cases F'_a,
                {
                    cases h2,
                    cases h2_a, -- A nat cannot ne evaluated any further
                    specialize ih2 _ _ h1_a h2_a,
                    simp [ih2]
                },
                {
                    cases h2,
                    cases h2_a,
                }
            }
        },
        {
            cases E2',
            {
                cases h2,
                {
                    rw ← h1_a,
                    rw ← h2_a,
                },
            },
            {
                cases h2;
                cases h2_a,
            },
        }
    }
end 
