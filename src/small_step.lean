import while

inductive w_exp_small : Type
    | nat : ℕ → w_exp_small
    | add : w_exp_small → w_exp_small → w_exp_small

open w_exp_small

inductive s_eval : w_exp_small → w_exp_small → Prop
    | s_left : ∀ E1 E2 E1' : w_exp_small, s_eval E1 E1' → s_eval (add E1 E2) (add E1' E2)
    | s_right : ∀ n : ℕ, ∀ E2 E2' : w_exp_small, s_eval E2 E2' → s_eval (add (nat n) E2) (add (nat n) E2')
    | s_num : ∀ p q r : ℕ, p + q = r →  s_eval (add (nat p) (nat q)) (nat r)

def normal_form (E : w_exp_small) : Prop := ∀ E' : w_exp_small, ¬ s_eval E E'

theorem s_step_determinacy : ∀ E E1 E2 : w_exp_small, s_eval E E1 → s_eval E E2 → E1 = E2 :=
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
                    exact ih1 _ _ h1_ᾰ h2_ᾰ,
                rw help,
            },
            -- The other cases are when E2' are n + E or n
            -- This means E1 is n and cannot be evaluated any further
            repeat {cases h1_ᾰ},
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
                cases h1_ᾰ,
            },
            {
                -- This is the case when F' = E + E
                cases F'_ᾰ,
                {
                    -- This is the case when F'_a is a nat
                    -- Since we have a + in h2, this means that we got here from the s_left or s_right case
                        cases h2,
                    {
                        -- Here we prove it cannot be the s_left case
                        cases h2_ᾰ, -- A nat cannot be evaluated any further
                    },
                    {
                        -- We use the inductive hypothesis to prove the s_right case
                        specialize ih2 _ _ h1_ᾰ h2_ᾰ,
                        rw ih2,
                    }
                },
                {
                    -- This is the case when F'_a is E + E
                    -- This means a nat reduces to another expression, which is not possible
                    cases h2,
                    cases h2_ᾰ,
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
                    rw ← h1_ᾰ,
                    rw ← h2_ᾰ,
                },
            },
            {
                -- This is the case E2' is E + E
                cases h2;
                cases h2_ᾰ,
            },
        }
    }
end 