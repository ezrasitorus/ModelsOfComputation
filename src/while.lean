import tactic

inductive w_exp : Type
    | nat : ℕ → w_exp
    | add : w_exp → w_exp → w_exp
    | mul : w_exp → w_exp → w_exp

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