import BernsteinGlobalExample
import BernsteinVsMonomial

open BernsteinCertificate BernsteinGlobalExample

-- Passing optimized and baseline Bernstein certificates.
#eval check coeff (5/13) (12/13) 5
#eval check baselineCoeff (1/3) (14/15) 5
-- Invalid coefficient, underestimated rate, and undersized state box.
#eval check (fun i : Fin 6 => if i = 2 then 1 else coeff i) (5/13) (12/13) 5
#eval check coeff (5/13) (11/13) 5
#eval check coeff (5/13) (12/13) 4
-- The old absolute-syntax checker rejects the same polynomial update.
#eval BoxContractionChecker.check BernsteinVsMonomial.update 1 5 (12/13)
-- Valid contraction bounds do not themselves certify the requested target.
-- Changing the forcing requires a new, separate target identity proof.
#eval check coeff (1/4) (12/13) 5
