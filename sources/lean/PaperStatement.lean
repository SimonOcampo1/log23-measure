import LogarithmExtension.LogRatioMain

/- An ASCII restatement of the manuscript's main theorem, with its proof. -/
namespace Log23Paper

theorem logRatio_approximation_bound
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Exists fun Q : Nat => And (2 <= Q)
      (forall (p : Int) (q : Nat), Q <= q ->
        (q : Real)^(-(3+epsilon)) <=
          abs (Real.log 3 / Real.log 2 - (p : Real)/(q : Real))) := by
  exact LogarithmExtension.LogRatio.Main.logRatio_approximation_bound epsilon hepsilon

#print axioms logRatio_approximation_bound

end Log23Paper
