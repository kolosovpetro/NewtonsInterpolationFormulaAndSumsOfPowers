(* ::Package:: *)

BeginPackage["NewtonsInterpolationFormulaAndSumsOfPowers`"]

(* BEGIN: Newton's series and sums of powers package *)
FiniteDifferenceOfPowerOrderN::usage="Validates corollary:forward-finite-difference-of-power"
NewtonSeriesForMonomialReindexed::usage="Validates proposition:newton-series-for-monomial-reindexed"
NewtonSeriesForPowerInZero::usage="Validates corollary:newton-series-for-power-in-zero"
NewtonSeriesForPowerInZeroReversed::usage="Validates corollary:newton-series-for-power-in-zero-reversed"
NewtonSeriesForBinomial::usage="Validates corollary:newton-series-for-binomial"
CommutativityOfNewtonSeriesForBinomial::usage="Validates corollary:commutativity-of-newton-series-for-binomial"
NewtonSeriesForBinomialReversed::usage="Validates corollary:newton-series-for-binomial-reversed"
CommutativityOfNewtonSeriesForBinomialReversed::usage="Validates corollary:commutativity-of-newton-series-for-binomial-reversed"
NewtonSeriesForMonomial::usage="Validates corollary:newton-series-for-monomial"
NewtonSeriesForMonomialReversed::usage="Validates corollary:newton-series-for-monomial-reversed"
PartialPowerSumLHS::usage="Validates corollary:partial-power-sums-2"
PartialPowerSumRHS::usage="Validates corollary:partial-power-sums-2"
MultifoldSumOfPowersRecurrence::usage=""
MultifoldSumOfPowersViaDifference::usage=""
MultifoldSumOfPowersViaDifferenceLHS::usage=""
ShiftedHockeyStickIdentityLHS::usage=""
ShiftedHockeyStickIdentityRHS::usage=""
ShiftedHockeyStickIdentityRHS1::usage=""
ShiftedHockeyStickIdentityRHS2::usage=""
ShiftedHockeyStickIdentityRHS3::usage=""
ShiftedHockeyStickIdentityRHS4::usage=""
ShiftedHockeyStickIdentityRHS5::usage=""
SumsOfPowersViaFiniteDifference::usage="Validates theorem:sums-of-powers-via-finite-difference"
RFoldSumViaAlternatingBinomialCorrectionTerm::usage=""
RFoldSumViaAlternatingBinomialCorrectionTerm1::usage=""
DoubleSumsOfPowersViaFiniteDifference::usage=""
DoubleSumsOfPowersViaFiniteDifference1::usage=""
DoubleSumsOfPowersViaFiniteDifference2::usage=""
ShiftedHockeyStickIdentityLHS1::usage=""
ShiftedHockeyStickIdentityRHS6::usage=""
ShiftedHockeyStickIdentityRHS7::usage=""
SumsOfPowersViaFiniteDifference2::usage=""
DoubleSumsOfPowersViaFiniteDifference3::usage=""
DoubleSumsOfPowersViaFiniteDifference4::usage=""
DoubleSumsOfPowersViaFiniteDifference5::usage=""
TripleSumsOfPowersViaFiniteDifference2::usage=""
TripleSumsOfPowersViaFiniteDifference21::usage=""
TripleSumsOfPowersViaFiniteDifference22::usage=""
TripleSumsOfPowersViaFiniteDifference23::usage=""
TripleSumsOfPowersViaFiniteDifference24::usage=""
PartialRFoldSumViaAlternatingBinomialCorrectionTerm::usage=""
FiniteDifferencesViaStirlingNumbers::usage=""
FiniteDifferencesViaStirlingNumbersReindexed::usage=""
R::usage=""
RFoldSumViaAlternatingBinomialCorrectionTerm2::usage=""
RFoldSumViaAlternatingBinomialCorrectionTerm3::usage=""
RFoldSumViaAlternatingBinomialCorrectionTerm4::usage=""
VanishingCorrectionCaseOfTheRFoldSum::usage=""
MultifoldSumsOfPowersViaNewtonsSeries::usage=""
ValidateMultifoldSumsOfPowersViaNewtonsSeries::usage=""
ValidateFiniteDifferenceViaStirlingNumbers::usage=""
EulerianNumber::usage=""
FiniteDifferenceViaEulerianNumbers::usage=""
ValidateFiniteDifferenceViaEulerianNumbers::usage=""
(* END: Newton's series and sums of powers package *)
(* =========================================================================DOCS END=================================================================== *)

(*BEGIN: Define 0^x = 1 for all x *)
Begin["`Private`"]
Unprotect[Power];
Power[0|0., 0|0.] = 1;
Protect[Power];
(*END: Define 0^x = 1 for all x *)

(* =========================================================================FUNCTIONS BEGIN=========================================================== *)

(* BEGIN: Newton's series and sums of powers package *)
FiniteDifferenceOfPowerOrderN[variable_, exp_, order_]:= Sum[(-1)^(order-j) * Binomial[order, j] * (variable+j)^(exp), {j, 0, order}];
NewtonSeriesForMonomialReindexed[n_, t_, m_]:= Sum[Binomial[t,k]*FiniteDifferenceOfPowerOrderN[n-t,m,k], {k,0,m}];
NewtonSeriesForPowerInZero[n_, m_]:= Sum[Binomial[n, m-k] * FiniteDifferenceOfPowerOrderN[0, m, m-k], {k, 0, m}];
NewtonSeriesForPowerInZeroReversed[n_, m_]:= Sum[Binomial[n, k] * FiniteDifferenceOfPowerOrderN[0, m, k], {k, 0, m}];
NewtonSeriesForBinomial[n_, t_, m_]:= Sum[Binomial[n, m-k] * FiniteDifferenceOfPowerOrderN[t, m, m-k], {k, 0, m}];
CommutativityOfNewtonSeriesForBinomial[n_, t_, m_]:= Sum[Binomial[t, m-k] * FiniteDifferenceOfPowerOrderN[n, m, m-k], {k, 0, m}];
NewtonSeriesForBinomialReversed[n_, t_, m_]:= Sum[Binomial[n, k] * FiniteDifferenceOfPowerOrderN[t, m, k], {k, 0, m}];
CommutativityOfNewtonSeriesForBinomialReversed[n_, t_, m_]:= Sum[Binomial[t, k] * FiniteDifferenceOfPowerOrderN[n, m, k], {k, 0, m}];
NewtonSeriesForMonomial[n_, t_, m_]:= Sum[Binomial[n-t, m-k] * FiniteDifferenceOfPowerOrderN[t, m, m-k], {k, 0, m}];
NewtonSeriesForMonomialReversed[n_, t_, m_]:= Sum[Binomial[n-t, k] * FiniteDifferenceOfPowerOrderN[t, m, k], {k, 0, m}];
PartialPowerSumLHS[n_, t_, exp_]:= Sum[k^(exp), {k, t, n}];
PartialPowerSumRHS[n_, t_, exp_]:= Sum[Binomial[n-t+1, k+1]* FiniteDifferenceOfPowerOrderN[t, exp, k], {k, 0, exp}];
MultifoldSumOfPowersRecurrence[r_, n_, m_]:= 0;
MultifoldSumOfPowersRecurrence[r_, n_, m_]:= n^m /; r==0;
MultifoldSumOfPowersRecurrence[r_, n_, m_]:= Sum[MultifoldSumOfPowersRecurrence[r-1, k, m], {k, 1, n}] /; r>0;
MultifoldSumOfPowersViaDifference[r_, n_, m_, t_]:=Sum[Binomial[n-t+r, k+r] * FiniteDifferenceOfPowerOrderN[t, m, k], {k, 0, m}];
MultifoldSumOfPowersViaDifferenceLHS[r_, n_, m_, t_]:= MultifoldSumOfPowersRecurrence[r, n, m] - MultifoldSumOfPowersRecurrence[r, t-1, m];
ShiftedHockeyStickIdentityLHS[t_, j_, n_]:= Sum[Binomial[-t+k, j], {k, 0, n}];
ShiftedHockeyStickIdentityRHS[t_, j_, n_]:= Sum[Binomial[-t+k, j], {k, 0, t-1}] + Sum[Binomial[-t+k, j], {k, t, n}];
ShiftedHockeyStickIdentityRHS1[t_, j_, n_]:= Sum[Binomial[-k-1, j], {k, 0, t-1}] + Sum[Binomial[-t+k, j], {k, t, n}];
ShiftedHockeyStickIdentityRHS2[t_, j_, n_]:= (-1)^j * Sum[Binomial[j+k, j], {k, 0, t-1}] + Sum[Binomial[-t+k, j], {k, t, n}];
ShiftedHockeyStickIdentityRHS3[t_, j_, n_]:= (-1)^j * Binomial[j+t, j+1] + Sum[Binomial[-t+k, j], {k, t, n}];
ShiftedHockeyStickIdentityRHS4[t_, j_, n_]:= (-1)^j * Binomial[j+t, j+1] + Sum[Binomial[k, j], {k, 0, n-t}];
ShiftedHockeyStickIdentityRHS5[t_, j_, n_]:= (-1)^j * Binomial[j+t, j+1] + Binomial[n-t+1, j+1];
SumsOfPowersViaFiniteDifference[n_, t_, m_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t, j+1] + Binomial[n-t+1, j+1]), {j, 0, m}];
RFoldSumViaAlternatingBinomialCorrectionTerm[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((Sum[(-1)^(j+s-1) * Binomial[j+t-1, j+s]*MultifoldSumOfPowersRecurrence[r-s, n, 0], {s, 1, r}] + Binomial[n-t+r, j+r])), {j, 0, m}];
RFoldSumViaAlternatingBinomialCorrectionTerm1[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((Sum[(-1)^(j+s-1) * Binomial[j+t, j+s], {s, 0, r}] 
+ Binomial[n-t+r, j+r])), {j, 0, m}];
DoubleSumsOfPowersViaFiniteDifference[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * Sum[((-1)^j * Binomial[j+t, j+1] + Binomial[k-t+1, j+1]), {k, 0, n}], {j, 0, m}];
DoubleSumsOfPowersViaFiniteDifference1[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t, j+1] * n + Sum[Binomial[k-t+1, j+1], {k, 0, n}]), {j, 0, m}];
DoubleSumsOfPowersViaFiniteDifference2[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t, j+1] * n + (-1)^(j+1) * Binomial[j+t, j+2] + Binomial[n-t+2, j+2]), {j, 0, m}];
ShiftedHockeyStickIdentityLHS1[t_, j_, n_]:= Sum[Binomial[-t+k, j], {k, 1, n}];
ShiftedHockeyStickIdentityRHS6[t_, j_, n_]:= Sum[Binomial[-t+k+1, j], {k, 0, n-1}];
ShiftedHockeyStickIdentityRHS7[t_, j_, n_]:= (-1)^(j)*Binomial[j+t-1, j+1] + Binomial[n-t+1, j+1];
SumsOfPowersViaFiniteDifference2[n_, t_, m_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t-1, j+1] + Binomial[n-t+1, j+1]), {j, 0, m}];
DoubleSumsOfPowersViaFiniteDifference3[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * Sum[((-1)^j * Binomial[j+t, j+1] + Binomial[k-t+1, j+1]), {k, 1, n}], {j, 0, m}];
DoubleSumsOfPowersViaFiniteDifference4[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t-1, j+1] * n + Sum[Binomial[k-t+1, j+1], {k, 1, n}]), {j, 0, m}];
DoubleSumsOfPowersViaFiniteDifference5[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t-1, j+1] * n + (-1)^(j+1)* Binomial[j+t-1, j+2] + Binomial[n-t+2, j+2]), {j, 0, m}];
TripleSumsOfPowersViaFiniteDifference2[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * Sum[(-1)^j * Binomial[j+t-1, j+1] k^1 + (-1)^(j+1) * Binomial[j+t-1, j+2]*k^0 + Binomial[k-t+2, j+2], {k, 1, n}], {j, 0, m}];
TripleSumsOfPowersViaFiniteDifference21[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * (-1)^j * Binomial[j+t-1, j+1] * MultifoldSumOfPowersRecurrence[2, n, 0] + (-1)^(j+1) * Binomial[j+t-1, j+2]* MultifoldSumOfPowersRecurrence[1, n, 0] + (-1)^(j+2) * Binomial[j+t-1, j+3] * MultifoldSumOfPowersRecurrence[0, n, 0] + Binomial[n-t+3, j+3], {j, 0, m}];
TripleSumsOfPowersViaFiniteDifference22[n_, t_, m_] :=
Sum[
  FiniteDifferenceOfPowerOrderN[t, m, j]*
   Sum[
    (-1)^j*Binomial[j + t - 1, j + 1]*k +
    (-1)^(j + 1)*Binomial[j + t - 1, j + 2] +
    Binomial[k - t + 2, j + 2],
    {k, 1, n}
   ],
  {j, 0, m}
];
TripleSumsOfPowersViaFiniteDifference23[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t-1, j+1] * (1/2*(n^2+n)) + (-1)^(j+1) * Binomial[j+t-1, j+2]*n + (-1)^(j+2) * Binomial[j+t-1, j+3] + Binomial[n-t+3, j+3]), {j, 0, m}];
TripleSumsOfPowersViaFiniteDifference24[n_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((-1)^j * Binomial[j+t-1, j+1] * MultifoldSumOfPowersRecurrence[2, n, 0] + (-1)^(j+1) * Binomial[j+t-1, j+2]* MultifoldSumOfPowersRecurrence[1, n, 0] + (-1)^(j+2) * Binomial[j+t-1, j+3] * MultifoldSumOfPowersRecurrence[0, n, 0] + Binomial[n-t+3, j+3]), {j, 0, m}];
PartialRFoldSumViaAlternatingBinomialCorrectionTerm[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((Sum[(-1)^(j+s-1) * Binomial[j+t, j+s]*MultifoldSumOfPowersRecurrence[r-s, n, 0], {s, 1, r}] + Binomial[n-t+r, j+r])), {j, 0, m}];
FiniteDifferencesViaStirlingNumbers[n_, k_, x_]:= Sum[Binomial[x, t-k] * StirlingS2[n, t] * t!, {t, 0, n}];
FiniteDifferencesViaStirlingNumbersReindexed[n_, k_, x_]:= Sum[Binomial[x, t] * StirlingS2[n, k+t] * (k+t)!, {t, 0, n}];
R[t_, n_, j_, r_] := Sum[(-1)^(j+s-1) * Binomial[j+t-1, j+s] * MultifoldSumOfPowersRecurrence[r-s, n, 0], {s,1,r}]+ Binomial[n-t+r, j+r];
RFoldSumViaAlternatingBinomialCorrectionTerm2[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * R[t, n, j, r], {j, 0, m}];
RFoldSumViaAlternatingBinomialCorrectionTerm3[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((Sum[(-1)^(j+s-1) * Binomial[j+t-1, j+s]*Binomial[r-s+n-1, r-s], {s, 1, r}] + Binomial[n-t+r, j+r])), {j, 0, m}];
RFoldSumViaAlternatingBinomialCorrectionTerm4[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((Sum[(-1)^(j+s) * Binomial[j+t-1, j+s+1]*Binomial[r-s+n-2, r-s-1], {s, 0, r-1}] + Binomial[n-t+r, j+r])), {j, 0, m}];
VanishingCorrectionCaseOfTheRFoldSum[r_, t_, m_] := Sum[FiniteDifferenceOfPowerOrderN[t, j, m] * Sum[(-1)^(j+s-1) * Binomial[j+t-1, j+s]*MultifoldSumOfPowersRecurrence[r-s, 1, 0], {s, 1, r}], {j, 0, m}];
MultifoldSumsOfPowersViaNewtonsSeries[r_, n_, m_, t_]:= Sum[FiniteDifferenceOfPowerOrderN[t, m, j] * ((Sum[(-1)^(j+s-1) * Binomial[j+t-1, j+s]*MultifoldSumOfPowersRecurrence[r-s, n, 0], {s, 1, r}] + Binomial[n-t+r, j+r])), {j, 0, m}];
ValidateMultifoldSumsOfPowersViaNewtonsSeries[r_] := Table[MultifoldSumOfPowersRecurrence[r,n,m]-MultifoldSumsOfPowersViaNewtonsSeries[r,n,m,t],{n,0,10},{m,0,10},{t,0,n}]//Flatten
ValidateFiniteDifferenceViaStirlingNumbers[t_]:= Table[FiniteDifferencesViaStirlingNumbersReindexed[n,k, t] - FiniteDifferenceOfPowerOrderN[t, n,k], {n, 0, 20}, {k, 0, n}] //Flatten
EulerianNumber[0, 0] = 1;
EulerianNumber[n_, k_] /; k < 0 || k >= n := 0;
EulerianNumber[n_, k_] := EulerianNumber[n, k] =
  (k + 1) EulerianNumber[n - 1, k] + (n - k) EulerianNumber[n - 1, k - 1];
FiniteDifferenceViaEulerianNumbers[m_, j_, t_]:= Sum[EulerianNumber[m,k]* Binomial[t+k, m-j], {k, 0, m}]; 
ValidateFiniteDifferenceViaEulerianNumbers[t_]:=Table[FiniteDifferenceViaEulerianNumbers[n,k, t]-FiniteDifferenceOfPowerOrderN[t, n,k], {n, 0, 20}, {k, 0, n}] //Flatten
(* END: Newton's series and sums of powers *)

End[ ]
EndPackage[ ]






