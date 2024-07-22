
theory Examples1
imports
  "Hybrid-Verification.Hybrid_Verification"
  "CAS-Integration.ODE_Solve_Keyword"
begin

dataspace ex =
  variables
    y :: real
    x :: real
    \<tau> :: real

context ex 
begin

ode_solve_thm "\<lambda> (t::real) x. (x + t)"

ode_solve_thm "{y` = - 2 * sin(2*pi*x)} \<^bold>{True\<^bold>}"


end

end