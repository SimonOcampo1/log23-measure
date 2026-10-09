import LogarithmExtension.Endpoint

/-! Conversion of any finite eventual approximation bound to the reference
irrationality exponent, not just to the special value two. -/

namespace LogarithmExtension

theorem finite_goodRationalApproximations_of_bound {x bound ν : ℝ}
    (hx : EventualLowerBound x bound) (hν : bound < ν) (hνpos : 0 < ν) :
    (OAI.PiExponent.GoodRationalApproximations x ν).Finite := by
  obtain ⟨Q, _, hb⟩ := hx ν hν
  apply (OAI.PiExponent.finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hlt : r.den < Q := by
    by_contra hn
    have h := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hlt.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)

theorem irrationalityExponent_le_of_eventualLowerBound {x bound : ℝ}
    (hx : EventualLowerBound x bound) :
    OAI.PiExponent.irrationalityExponent x ≤ bound := by
  have htwo := OAI.PiExponent.two_mem_approximationExponents (irrational_of_eventualLowerBound hx)
  apply csSup_le ⟨2, htwo⟩
  intro ν hν
  by_contra h
  exact (finite_goodRationalApproximations_of_bound hx (by linarith) hν.1).not_infinite hν.2

theorem two_le_irrationalityExponent_of_eventualLowerBound {x bound : ℝ}
    (hx : EventualLowerBound x bound) :
    2 ≤ OAI.PiExponent.irrationalityExponent x := by
  have htwo := OAI.PiExponent.two_mem_approximationExponents (irrational_of_eventualLowerBound hx)
  apply le_csSup (a := (2 : ℝ)) ?_ htwo
  refine ⟨bound, ?_⟩
  intro ν hν
  by_contra h
  exact (finite_goodRationalApproximations_of_bound hx (by linarith) hν.1).not_infinite hν.2

#print axioms irrationalityExponent_le_of_eventualLowerBound

end LogarithmExtension
