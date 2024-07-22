
theory Reactive
  imports 
     "Hybrid-Verification.Hybrid_Verification"
     "Z_Toolkit.Trace_Algebra"
begin

dataspace Reactive =
  variables
    wait :: bool
    tr   :: "'t::trace"

context Reactive
begin

abbreviation "pre e \<equiv> tr ::= (tr + e)"

definition prefixing :: "('st \<Rightarrow> 't) \<Rightarrow> 'st \<Rightarrow> 'st set"
  where "prefixing e = tr ::= (tr + e)"

dataspace CSPT = Reactive +
  variables
    ex :: bool

end