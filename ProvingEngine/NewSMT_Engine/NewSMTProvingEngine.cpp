#include <string>
#include <cstring>
#include "NewSMTProvingEngine.h"
#include "../STL_Engine/STL_FactsDatabase.h"
#include "../SMTOut.h"
#include "CLProof/CLProof.h"
#include "CLTheory/Theory.h"
#include "common.h"


// ---------------------------------------------------------------------------------------

NewSMTProvingEngine::NewSMTProvingEngine(Theory *pT, proverParams &params) {
  // FIXME! this is temporary, always fixed
  mSMT_theory = eSMTBV_ProvingEngine;

  mpT = pT;
  mParams = params;
  mnNumberOfAssumptions = 0;
  mSMT_theory = mParams.eEngine;
  if (mSMT_theory == eSMTLIA_ProvingEngine)
    mName = "QF_LIA";
  else if (mSMT_theory == eSMTUFLIA_ProvingEngine)
    mName = "QF_UFLIA";
  else if (mSMT_theory == eSMTBV_ProvingEngine)
    mName = "QF_BV";
  else if (mSMT_theory == eSMTUFBV_ProvingEngine)
    mName = "QF_UFBV";
  else
      mName = "UNKNOWN";
  mSMT_theory = params.eEngine;


  // FIXME! this is temporary, always fixed
  mSMT_theory = eSMTBV_ProvingEngine;
  mName = "QF_BV";

  //mSMTout.SetTheory(mSMT_theory);
  for(auto it = pT->mSignature.begin(); it < pT->mSignature.end(); it++)
      if (mnMaxArity < it->second)
          mnMaxArity = it->second;
}

// ---------------------------------------------------------------------------------------

void NewSMTProvingEngine::SetStartTimeAndLimit(const clock_t &startTime,
                                             unsigned timeLimit) {
  mStartTime = startTime;
  mParams.time_limit = timeLimit;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::CorrectnessCondition()
{
    Constraint c;
    // 1. Each proof step s is one of the defined step kinds
    for(unsigned s = mnNumberOfAssumptions; s < mnNumberOfAssumptions + mProofLength; s++)
      c &= CorrectProofStep(s);

    for(unsigned s = mnNumberOfAssumptions + 1; s < mnNumberOfAssumptions + mProofLength; s++)
      c &= ((IsQEDStep(s - 1) == False()) | (Nesting(s - 1) != Nesting(s)))
           << "2: If step s-1 is one of the QED steps, then Nesting (s-1) != Nesting (s):";

    for(unsigned s = mnNumberOfAssumptions + 1; s < mnNumberOfAssumptions + mProofLength; s++)
      c &= ((Cases(s - 1) == False()) | (StepKind(s) == FirstCase()))
           << "3: If Cases(s-1) is true, then StepKind(s) = FirstCase ";

    for(unsigned s = mnNumberOfAssumptions + 1; s < mnNumberOfAssumptions + mProofLength; s++)
      c &= ((IsQEDStep(s - 1) == False()) | (OddNesting(s - 1)) |
           (StepKind(s) == SecondCase()))
           << "4: If step s-1 is one of the QED steps and Nesting(s-1) is even, then StepKind(s) = SecondCase";

    for(unsigned s = mnNumberOfAssumptions + 1; s < mnNumberOfAssumptions + mProofLength; s++)
      c &= ((IsQEDStep(s - 1) == False()) | (OddNesting(s-1) == False()) |
           (StepKind(s) == QEDbyCases()))
           << "5: If step s-1 is one of the QED steps and Nesting(s-1) is odd, then StepKind(s) = QEDbyCases";

    Constraint cAllL;
    for(unsigned L = mnNumberOfAssumptions + 1; L <= mnNumberOfAssumptions + mProofLength; L++) {
      // For each possible proof length L up to mProofLength
      Constraint cOneL;
      cOneL &= (Nesting(L - 1) == 1u)
            << "   6: Nesting(L-1) = 1";

      cOneL &= IsQEDStep(L - 1)
            << "   7: The step L-1 is one of the QED steps";

      Constraint cc;
      cc &= ContentsPredicate(L - 1, 0) == ContentsPredicate(mnNumberOfAssumptions + mProofLength - 1, 0);
      cc &= ContentsPredicate(L - 1, 1) == ContentsPredicate(mnNumberOfAssumptions + mProofLength - 1, 1);
      for(unsigned j=0; j < mGoal.GetElement(0).GetElement(0).GetArity(); j++) {
        cc &= (ContentsArgument(L - 1, 0, j) == ContentsArgument(mnNumberOfAssumptions + mProofLength - 1, 0, j));
        cc &= (ContentsArgument(L - 1, 1, j) == ContentsArgument(mnNumberOfAssumptions + mProofLength - 1, 1, j));
      }
      if (mnNumberOfAssumptions + mProofLength >= 2)
        cc = (cc << "   8: Contents(L-1) = Contents(MaxL-1)");
      cOneL &= cc;
      cAllL |= cOneL;
    }
    c &= cAllL;
    return c << "\n ; ***************** Correctness constraints: ";
}

// ----------------------------------------------------------

Constraint NewSMTProvingEngine::CorrectProofStep(unsigned s)
{
    return
      ( //IsAssumption(s) | // Assumptions are constrained by AddPremise
        IsMPstep(s)
      | IsFirstCase(s)
      | IsSecondCase(s)
      | IsQEDbyCases(s)
      | IsQEDbyAssumption(s)
      | IsQEDbyEFQ(s))
      << "; ************ Is step " + itos(s) + " correct ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsAssumption(unsigned s)
{
    Constraint c(False());
    for(unsigned i=0; i < mnNumberOfAssumptions; i++)
      c |= IsAssumptionStep(s, i);
    if (mnNumberOfAssumptions > 0)
      c = (c << "Is Assumption step: ");
    return c;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsAssumptionStep(unsigned s, unsigned i)
{
    return
        (StepKind(s) == Assumption())
      & (Cases(s) == False())
      & (Nesting(s) == 1u)
      & (SameContents(s,0,i,0));
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsMPstep(unsigned s)
{
    Constraint c;
    for(unsigned k = 0; k < mpT->mCLaxioms.size(); k++)
      c |= IsMPstepByAxiom(s,k);
    return c;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsMPstepByAxiom(unsigned s, unsigned k)
{
    Constraint c =
         (StepKind(s) == MP())
       & (AxiomApplied(s) == k)
       & (Cases(s) == (GetAxiom(k).GetGoal().GetSize() > 1))
       & (s>0 ? Nesting(s) == Nesting(s-1) : Nesting(s) == 1u)
       & (MatchConclusion(s,k))
       & (MatchAllPremises(s,k));
    return c << "Is axiom " + itos(k) + " applied: ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::MatchConclusion(unsigned s, unsigned k)
{
    Constraint c;
    c = (ContentsPredicate(s,0) == GetAxiom(k).GetGoal().GetElement(0).GetElement(0).GetName());
    for(unsigned j=0; j < GetAxiom(k).GetGoal().GetElement(0).GetElement(0).GetArity(); j++) {
      if (BindingAxiomGoal(k, 0, j) != 0)
        c &= (ContentsArgument(s,0,j) == Instantiation(s,BindingAxiomGoal(k, 0, j)-1));
      else // it is a constant
        c &= (ContentsArgument(s,0,j) == CONSTANTS[GetAxiom(k).GetGoal().GetElement(0).GetElement(0).GetArg(j)]);
    }
    if (GetAxiom(k).GetGoal().GetSize() > 1) {
        c &= (ContentsPredicate(s,1) == GetAxiom(k).GetGoal().GetElement(1).GetElement(0).GetName());
        for(unsigned j=0; j < GetAxiom(k).GetGoal().GetElement(1).GetElement(0).GetArity(); j++)
          if (BindingAxiomGoal(k, 1, j) != 0)
            c &= (ContentsArgument(s,1,j) == Instantiation(s,BindingAxiomGoal(k, 1, j)-1));
          else // it is a constant
            c &= (ContentsArgument(s,1,j) == CONSTANTS[GetAxiom(k).GetGoal().GetElement(1).GetElement(0).GetArg(j)]);
    }
    return c;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::MatchAllPremises(unsigned s, unsigned k)
{
    Constraint c = True();
    for(unsigned i=0; i < GetAxiom(k).GetPremises().GetSize(); i++)
        c &= MatchPremiseToSomeStep(s,k,i);
    return c;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::MatchPremiseToSomeStep(unsigned s, unsigned k, unsigned i)
{
    Constraint c = False();
    for(unsigned ss=0; ss < s; ss++)
      c |= MatchPremiseToStep(s, k, i, ss);
    return c;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::MatchPremiseToStep(unsigned s, unsigned k, unsigned i, unsigned ss)
{
    Constraint c;
    if (GetAxiom(k).GetPremises().GetElement(i).GetName() == "true")
      c = True();
    else {
      c = (From(s,i) == ss)
        & (Cases(ss) == False())
        & (SameBranch(ss,s))
        & (ContentsPredicate(ss,0) == GetAxiom(k).GetPremises().GetElement(i).GetName());
      for(unsigned j=0; j < GetAxiom(k).GetPremises().GetElement(i).GetArity(); j++) {
        if (BindingAxiomPremises(k, i, j) != 0)
          c &= (ContentsArgument(ss,0,j) == Instantiation(s,BindingAxiomPremises(k, i, j)-1));
        else // it is a constant
         c &= (ContentsArgument(ss,0,j) == CONSTANTS[GetAxiom(k).GetPremises().GetElement(i).GetArg(j)]);
      }
    }
    return c;
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::SameContents(unsigned step1, unsigned part1, unsigned step2, unsigned part2)
{
    Constraint c = (ContentsPredicate(step1,part1) == ContentsPredicate(step2,part2));
    for(unsigned int i = 0; i < mnMaxArity; i++)
      c &= (ContentsArgument(step1,part1,i) == ContentsArgument(step2,part2,i));
    return c;
}

// ---------------------------------------------------------------------------------------

unsigned NewSMTProvingEngine::BindingAxiomPremises(unsigned ax, unsigned premise, unsigned arg)
{
    return mBindingAx[ax][premise][arg];
}

// ---------------------------------------------------------------------------------------

unsigned NewSMTProvingEngine::BindingAxiomGoal(unsigned ax, unsigned goal, unsigned arg)
{
    return mBindingAxGoal[ax][goal][arg];
}

// -----------------------------------------------------------------

Constraint NewSMTProvingEngine::IsFirstCase(unsigned s)
{
    Constraint c =
         (s == 0) ?
           (False())
         : (StepKind(s) == FirstCase())
           & (StepKind(s - 1) == MP())
           & (Cases(s - 1) == True())
           & (Cases(s) == False())
           & (Nesting(s) == Nesting(s - 1) * 2u)
           & (SameContents(s,0,s - 1,0));
    return c << "Is it first case: ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsSecondCase(unsigned s)
{
    Constraint c;
    if (s == 0)
        c = (False());
    else {
        Constraint cMatchMP;
        for (unsigned int ss=0; ss+2 < s; ss++) {
          cMatchMP |= (StepKind(ss) == MP())
                    & (Cases(ss) == True())
                    & (SameContents(s,0,ss,1));
        }
        c = (StepKind(s) == SecondCase())
            & (IsQEDStep(s-1))
            & cMatchMP
            & (Cases(s) == False())
            & (OddNesting(s)) // This condition is missing in the paper!
            & (Nesting(s) == Nesting(s-1) + 1u);
    }
    return c << "Is it second case: ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsQEDbyCases(unsigned s)
{
    Constraint c =
      (s == 0) ?
        (False())
      : (StepKind(s) == QEDbyCases())
      & (IsQEDStep(s-1))
      & (IsGoal(s))
      & (OddNesting(s - 1))
      & (Nesting(s) * 2u + 1u == Nesting(s-1));
    return c << "Is it QED by cases: ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsQEDbyAssumption(unsigned s)
{
    Constraint c;
    if (s == 0) {
      if (mGoal.GetElement(0).GetElement(0).GetName() == "true") // special case: goal = "true"
        c = ((StepKind (s) == QEDbyAssumption())
           & (Nesting(s) == 1u));
      else
        c = False();
    }
    else {
      c = (StepKind (s) == QEDbyAssumption())
        & (IsGoal(s - 1))
        & (IsGoal(s))
        & (Nesting(s) == Nesting(s - 1));
    }
    return c << "Is it QED by assumption: ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsQEDbyEFQ(unsigned s)
{
    Constraint c =
      (s == 0) ?
        (False())
      : (StepKind(s) == QEDbyEFQ())
      & (ContentsPredicate(s - 1,0) == Bot())
      & (IsGoal(s))
      & (Nesting(s) == Nesting(s-1));
    return c << "Is it QED by EFQ: ";
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::IsQEDStep(unsigned s)
{
   return
       (StepKind(s) == QEDbyCases())
     | (StepKind(s) == QEDbyAssumption())
     | (StepKind(s) == QEDbyEFQ());
}

// ---------------------------------------------------------------------------------------

Constraint NewSMTProvingEngine::StepKind(unsigned s)
{
    return Constraint("StepKind_l_" + itos(s) + "_r_");
}
Constraint NewSMTProvingEngine::From(unsigned s, unsigned i)
{
    return Constraint("From_l_" + itos(s) + + "_r__l_" + itos(i) + "_r_");
}
Constraint NewSMTProvingEngine::AxiomApplied(unsigned s)
{
    return Constraint("AxiomApplied_l_" + itos(s) + "_r_");
}
Constraint NewSMTProvingEngine::Instantiation(unsigned s, unsigned var)
{
    return Constraint("Instantiation_l_" + itos(s) + "_r__l_" + itos(var) + "_r_");
}
Constraint NewSMTProvingEngine::Cases(unsigned s)
{
    return Constraint("Cases_l_" + itos(s) + "_r_");
}
Constraint NewSMTProvingEngine::Nesting(unsigned s)
{
    return Constraint("Nesting_l_" + itos(s) + "_r_");
}
Constraint NewSMTProvingEngine::SameBranch(unsigned s1, unsigned s2)
{
    return Constraint("SameBranch_l_" + itos(s1) + "_r__l_" + itos(s2)+ "_r_");
}
Constraint NewSMTProvingEngine::OddNesting(unsigned s)
{
    return Constraint("OddNesting_l_" + itos(s) + "_r_");
}
Constraint NewSMTProvingEngine::IsGoal(unsigned s)
{
    return Constraint("IsGoal_l_" + itos(s) + "_r_");
}
Constraint NewSMTProvingEngine::ContentsPredicate(unsigned s, unsigned part)
{
    return Constraint("ContentsPredicate_l_" + itos(s) + "_r__l_" + itos(part)+ "_r_");
}
Constraint NewSMTProvingEngine::ContentsArgument(unsigned s, unsigned part, unsigned arg)
{
    return Constraint("ContentsArgument_l_" + itos(s) + "_r__l_" + itos(part) + "_r__l_" + itos(arg)+ "_r_");
}

// ----------------------------------------------------------

Constraint NewSMTProvingEngine::Assumption()
{
    return string("eAssumption");
}
Constraint NewSMTProvingEngine::MP()
{
    return string("eMP");
}
Constraint NewSMTProvingEngine::FirstCase()
{
    return string("eFirstCase");
}
Constraint NewSMTProvingEngine::SecondCase()
{
    return string("eSecondCase");
}
Constraint NewSMTProvingEngine::QEDbyCases()
{
    return string("eQEDbyCases");
}
Constraint NewSMTProvingEngine::QEDbyAssumption()
{
    return string("eQEDbyAssumption");
}
Constraint NewSMTProvingEngine::QEDbyEFQ()
{
    return string("eQEDbyEFQ");
}

// ----------------------------------------------------------

Constraint NewSMTProvingEngine::Bot()
{
    return string("false");
}
Constraint NewSMTProvingEngine::Top()
{
    return string("true");
}

// ----------------------------------------------------------

Constraint NewSMTProvingEngine::True()
{
    return Constraint(true);
}
Constraint NewSMTProvingEngine::False()
{
    return Constraint(false);
}

// ----------------------------------------------------------

const CLFormula& NewSMTProvingEngine::GetAxiom(unsigned k)
{
    return mpT->Axiom(k).first;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::ComputeBindingForAxioms()
{
    for (unsigned k = 0; k < mpT->NumberOfAxioms(); k++)
       ComputeBinding(GetAxiom(k),k);
}

// ----------------------------------------------------------

void NewSMTProvingEngine::ComputeBinding(const CLFormula &f, unsigned k) {
  for (size_t j = 0; j < f.GetPremises().GetSize(); j++) {
    for (size_t i = 0; i < f.GetPremises().GetElement(j).GetArity(); i++)
      if ((int)f.UnivVarOrdinalNumber(
              f.GetPremises().GetElement(j).GetArg(i)) != -1)
        mBindingAx[k][j][i] =
          f.UnivVarOrdinalNumber(f.GetPremises().GetElement(j).GetArg(i)) + 1;
      else {
        mBindingAx[k][j][i] = 0;
      }
  }
  if (f.GetGoal().GetSize() > 0) { // disjunctions in the goal can have only one disjunct
    for (size_t i = 0;
         i < f.GetGoal().GetElement(0).GetElement(0).GetArity(); i++) {
      if ((int)f.UnivVarOrdinalNumber(
              f.GetGoal().GetElement(0).GetElement(0).GetArg(i)) != -1)
        mBindingAxGoal[k][0][i] =
          f.UnivVarOrdinalNumber(f.GetGoal().GetElement(0).GetElement(0).GetArg(i)) + 1;
      else if ((int)f.ExistVarOrdinalNumber(
                   f.GetGoal().GetElement(0).GetElement(0).GetArg(i)) != -1)
        mBindingAxGoal[k][0][i] = f.GetNumOfUnivVars() +
          f.ExistVarOrdinalNumber(f.GetGoal().GetElement(0).GetElement(0).GetArg(i)) + 1;
      else {
        mBindingAxGoal[k][0][i] = 0;
      }
    }
  }
  if (f.GetGoal().GetSize() > 1) {
    for (size_t i = 0;
         i < f.GetGoal().GetElement(1).GetElement(0).GetArity(); i++) {
      if ((int)f.UnivVarOrdinalNumber(
              f.GetGoal().GetElement(1).GetElement(0).GetArg(i)) != -1)
        mBindingAxGoal[k][1][i] =
            f.UnivVarOrdinalNumber(
                f.GetGoal().GetElement(1).GetElement(0).GetArg(i)) +
            1;
      else if ((int)f.ExistVarOrdinalNumber(
                   f.GetGoal().GetElement(1).GetElement(0).GetArg(i)) != -1)
        mBindingAxGoal[k][1][i] =
            f.GetNumOfUnivVars() +
            f.ExistVarOrdinalNumber(
                f.GetGoal().GetElement(1).GetElement(0).GetArg(i)) +
            1;
      else {
        mBindingAxGoal[k][1][i] = 0;
      }
    }
  }
}

// ---------------------------------------------------------------------------------------

void NewSMTProvingEngine::AddPremise(const Fact &f) {
  mpT->AddSymbol(f.GetName(), f.GetArity());

  Constraint c;
  c = (StepKind(mnNumberOfAssumptions) == Assumption())
    & (Nesting(mnNumberOfAssumptions) == 1u)
    & (Cases(mnNumberOfAssumptions) == False())
    & (AxiomApplied(mnNumberOfAssumptions) == Assumption())
    & (ContentsPredicate(mnNumberOfAssumptions,0) == ToUpper(f.GetName()));
  for (size_t i = 0; i < f.GetArity(); i++)
    c &= (ContentsArgument(mnNumberOfAssumptions,0,i) == ToUpper(f.GetArg(i)));
  mConstraint &= c << "Assumption " + itos(mnNumberOfAssumptions);
  mnNumberOfAssumptions++;
}

// ---------------------------------------------------------------------------------------

bool NewSMTProvingEngine::ProveFromPremises(const DNFFormula& formula, CLProof& proof) {
  bool ret = false;
  if (mSMT_theory == eSMTLIA_ProvingEngine || mSMT_theory == eSMTUFLIA_ProvingEngine)
    mSMT_type = "Int";
  else if (mSMT_theory == eSMTBV_ProvingEngine || mSMT_theory == eSMTUFBV_ProvingEngine)
    mSMT_type = "(_ BitVec 12)";

  mGoal = formula;
  ComputeBindingForAxioms();

  if (system(NULL)) {

    if (formula.GetSize() > 0) // disjunctions in the goal can have only one disjunct
      mpT->AddSymbol(formula.GetElement(0).GetElement(0).GetName(),
                     formula.GetElement(0).GetElement(0).GetArity());
    if (formula.GetSize() > 1)
      mpT->AddSymbol(formula.GetElement(1).GetElement(0).GetName(),
                     formula.GetElement(1).GetElement(0).GetArity());

    time_t start_time = time(NULL);
    unsigned l, r, s, best = 0, best_start = 0;
    l = mParams.starting_proof_length;
    cout << "Looking for a proof of length: " << flush;
    while (l <= mParams.max_proof_length) {
      time_t current_time = time(NULL);
      double remainingTime = mParams.time_limit - difftime(current_time, start_time);
      if (remainingTime <= 0)
        break;

      string smt_proofencoded_filename = "gen-prove.smt"; // tmpnam(NULL); //
      string smt_model_filename = "gen-smt-model.txt";    // tmpnam(NULL); //
      mProofLength = l;
      EncodeProofToSMT(formula, l, smt_proofencoded_filename);
      const string sCall = "timeout " + to_string(remainingTime) + " z3  " +
                           smt_proofencoded_filename + " > " +
                           smt_model_filename;
      cout << l << flush;
      /*int rv =*/system(sCall.c_str());
      if (!ReadModel(smt_model_filename)) {
        l += 12;
        cout << ", " << flush;
      } else {
        cout << " (found), " << flush;
        best = l;
        break;
      }
    }

    if (mParams.shortest_proof && best) {
      r = best;
      best_start = best;
      ret = ReconstructProof(formula, proof);
      cout << endl << "Simplifying the proof (size without assumptions: "
           << proof.Size() - proof.NumOfAssumptions() << ")" << flush;
      proof.Simplify();
      cout << endl << "Done! (new proof length without assumptions: "
           << proof.Size() - proof.NumOfAssumptions() << ")" << endl;
      r = proof.Size() - proof.NumOfAssumptions();
      best = r;
      best_start = best;
      l = best / 2 + 1;

      if (l <= r && l != best)
        cout << "Looking for a proof of length: " << flush;
      while (l <= r && l != best) {
        time_t current_time = time(NULL);
        double remainingTime = mParams.time_limit - difftime(current_time, start_time);
        if (remainingTime <= 0)
          break;

        s = (l + r) / 2;
        string smt_proofencoded_filename = tmpnam(NULL);
        string smt_model_filename = tmpnam(NULL);
        mProofLength = l;
        EncodeProofToSMT(formula, l, smt_proofencoded_filename);
        const string sCall = "timeout " + to_string(remainingTime) + " z3  " +
                             smt_proofencoded_filename + " > " +
                             smt_model_filename;
        // cout << "Trying proof length " << s << ";" << flush;
        cout << s << flush;
        /*int rv =*/system(sCall.c_str());
        if (!ReadModel(smt_model_filename)) {
          l = s + 1;
          cout << " ";
        } else {
          cout << " (found), ";
          best = s;
          r = s - 1;
        }
      }
    }
    cout << endl;
    if (best > 0 && best != best_start) {
      cout << "Best found proof: of the length " << best << endl;
      ret = ReconstructProof(formula, proof);
      assert(ret);
    }
  }

  PREDICATE.clear();
  ARITY.clear();
  CONSTANTS.clear();

  mnMaxArity = 0;
  mnMaxNumberOfPremisesInAxioms = 0;
  mnNumberOfAssumptions = 0;
  return ret;
}

// ---------------------------------------------------------------------------------------

void NewSMTProvingEngine::EncodeProofToSMT(const DNFFormula &formula,
                                            unsigned nProofLen,
                                            string prove_smt_filename) {
    mSMTfile.open(prove_smt_filename);
    // smtFile << "(set-option :print-success false)" << endl;
    mSMTfile << "(set-option :produce-models true)" << endl;
    mSMTfile << "(set-logic " + mName + ")" << endl << endl;

    mnMaxArity = 0;
    for (size_t i = 0; i < mpT->mSignature.size(); i++) {
      if (mpT->mSignature[i].second > mnMaxArity)
        mnMaxArity = mpT->mSignature[i].second;
    }

    DeclareVarBasicType("neAssumption");
    DeclareVarBasicType("neNegIntro");
    DeclareVarBasicType("neFirstCase");
    DeclareVarBasicType("neSecondCase");
    DeclareVarBasicType("neEQSub");
    DeclareVarBasicType("neEQReflex");
    DeclareVarBasicType("neEQSymm");
    DeclareVarBasicType("neNegElim");
    DeclareVarBasicType("neExcludedMiddle");
    DeclareVarBasicType("neQEDbyCases");
    DeclareVarBasicType("neQEDbyAssumption");
    DeclareVarBasicType("neQEDbyEFQ");
    //DeclareVarBasicType("neQEDbyNegIntro");
    DeclareVarBasicType("neMP");
    DeclareVarBasicType("neNumberOfStepKind");

    AssertVarBasicType("neAssumption",       0x000);
    AssertVarBasicType("neNegIntro",         0x001);
    AssertVarBasicType("neFirstCase",        0x002);
    AssertVarBasicType("neSecondCase",       0x003);
    AssertVarBasicType("neEQSub",            0x004);
    AssertVarBasicType("neEQReflex",         0x005);
    AssertVarBasicType("neEQSymm",           0x006);
    AssertVarBasicType("neNegElim",          0x007);
    AssertVarBasicType("neExcludedMiddle",   0x008);
    AssertVarBasicType("neQEDbyCases",       0x009);
    AssertVarBasicType("neQEDbyAssumption",  0x00a);
    AssertVarBasicType("neQEDbyEFQ",         0x00b);
  //Assert("neQEDbyNegIntro",               0x000);
    AssertVarBasicType("neMP",               0x00c);
    AssertVarBasicType("neNumberOfStepKind", 0x00d);

    mnMaxNumberOfPremisesInAxioms = 0;
    for (vector<pair<CLFormula, string>>::iterator it = mpT->mCLaxioms.begin();
         it != mpT->mCLaxioms.end(); it++)
      if (it->first.GetPremises().GetSize() > mnMaxNumberOfPremisesInAxioms)
        mnMaxNumberOfPremisesInAxioms = it->first.GetPremises().GetSize();
    for (size_t i = 0; i < mpT->mSignature.size(); i++)
      DeclareVarBasicType(NUM_PREFIX + ToUpper(mpT->mSignature[i].first));
    for (vector<string>::const_iterator it = mpT->mConstants.begin();
         it != mpT->mConstants.end(); it++)
      DeclareVarBasicType(NUM_PREFIX + ToUpper(*it));
    for (set<string>::iterator it = mpT->mConstantsPermissible.begin();
         it != mpT->mConstantsPermissible.end(); it++)
      DeclareVarBasicType(NUM_PREFIX + ToUpper(*it));


    mnMaxNumberOfVarsInAxioms = 0;
    for (vector<pair<CLFormula, string>>::iterator it = mpT->mCLaxioms.begin();
         it != mpT->mCLaxioms.end(); it++) {
      unsigned num = it->first.GetNumOfUnivVars() + it->first.GetNumOfExistVars();
      if (num > mnMaxNumberOfVarsInAxioms)
          mnMaxNumberOfVarsInAxioms = num;
    }

    unsigned nFinalStep = mnNumberOfAssumptions + nProofLen - 1;
    for (unsigned i=0; i <= nFinalStep; i++) {
      DeclareVarBasicType(StepKind(i).toSMT());
      DeclareVarBasicType(AxiomApplied(i).toSMT());
      DeclareVarBasicType(Nesting(i).toSMT());
      DeclareVarBoolean(OddNesting(i).toSMT());
      for (unsigned j=i+1; j <= nFinalStep; j++) {
        DeclareVarBoolean(SameBranch(i,j).toSMT());
      }
      DeclareVarBasicType(ContentsPredicate(i,0).toSMT());
      DeclareVarBasicType(ContentsPredicate(i,1).toSMT());
      DeclareVarBoolean(Cases(i).toSMT());
      DeclareVarBoolean(IsGoal(i).toSMT());

      for (unsigned k=0; k < mnMaxArity; k++) {
        DeclareVarBasicType(ContentsArgument(i,0,k).toSMT());
        DeclareVarBasicType(ContentsArgument(i,1,k).toSMT());
      }
      for (unsigned k=0; k < mnMaxNumberOfVarsInAxioms; k++) {
        DeclareVarBasicType(Instantiation(i,k).toSMT());
      }
      for (unsigned j=0; j < mnMaxNumberOfPremisesInAxioms; j++) {
        DeclareVarBasicType(From(i,j).toSMT());
      }
    }

    // These constraints are generated once, since they are used in many conditions:
    for (unsigned i=0; i <= nFinalStep; i++) {
      Constraint c =
          (Nesting(i) == 1u) // fix me, make this more beatiful
        | (Nesting(i) == 3u)
        | (Nesting(i) == 7u)
        | (Nesting(i) == 9u)
        | (Nesting(i) == 11u);
      AssertVar(OddNesting(i), c);

      for (unsigned j=i+1; j <= nFinalStep; j++) {
        Constraint c =
            (Nesting(i) == Nesting(j))
          | ((Nesting(i) >= Nesting(j) * 2u) & (Nesting(i) < Nesting(j) * 2u + 2u))
          | ((Nesting(i) >= Nesting(j) * 4u) & (Nesting(i) < Nesting(j) * 4u + 4u))
          | ((Nesting(i) >= Nesting(j) * 8u) & (Nesting(i) < Nesting(j) * 8u + 8u))
          | ((Nesting(i) >= Nesting(j) *16u) & (Nesting(i) < Nesting(j) *16u + 16u));
          AssertVar(SameBranch(i,j), c);
      }
    }

    AddComment("************************* Predicate symbols **************************");
    unsigned enumerator = 0;
    for (size_t i = 0; i < mpT->mSignature.size(); i++) {
      AssertVar(NUM_PREFIX + ToUpper(mpT->mSignature[i].first),
                         itos(mSMT_theory, enumerator));
      ARITY[enumerator] = mpT->mSignature[i].second;
      PREDICATE[NUM_PREFIX + ToUpper(mpT->mSignature[i].first)] = enumerator++;
      if (mpT->mSignature[i].second > mnMaxArity)
        mnMaxArity = mpT->mSignature[i].second;
    }

    enumerator = 0;
    AddComment("***************************** Constants *******************************");
    for (vector<string>::const_iterator it = mpT->mConstants.begin();
         it != mpT->mConstants.end(); it++) {
      AssertVarBasicType(NUM_PREFIX + ToUpper(*it), enumerator);
      CONSTANTS[*it] = enumerator++;
    }
    for (set<string>::iterator it = mpT->mConstantsPermissible.begin();
         it != mpT->mConstantsPermissible.end(); it++) {
      AssertVarBasicType(NUM_PREFIX + ToUpper(*it), enumerator);
      CONSTANTS[*it] = enumerator++;
    }

    set<string> exi_vars;
    for (size_t i = 0; i < formula.GetElement(0).GetElement(0).GetArity(); i++) {
      if (CONSTANTS.find(formula.GetElement(0).GetElement(0).GetArg(i)) == CONSTANTS.end()
          && exi_vars.find(formula.GetElement(0).GetElement(0).GetArg(i)) == exi_vars.end()) {
        DeclareVarBasicType(NUM_PREFIX + ToUpper(formula.GetElement(0).GetElement(0).GetArg(i)));
        exi_vars.insert(formula.GetElement(0).GetElement(0).GetArg(i));
      }
    }
    if (formula.GetSize() > 1) {
      for (size_t i = 0; i < formula.GetElement(1).GetElement(0).GetArity(); i++) {
        if (CONSTANTS.find(formula.GetElement(1).GetElement(0).GetArg(i)) == CONSTANTS.end() &&
          exi_vars.find(formula.GetElement(1).GetElement(0).GetArg(i)) ==
                exi_vars.end()) {
          DeclareVarBasicType(NUM_PREFIX + ToUpper(formula.GetElement(1).GetElement(0).GetArg(i)));
          exi_vars.insert(formula.GetElement(1).GetElement(0).GetArg(i));
        }
      }
    }

    AddComment("");
    AddComment("****************************** Axioms *********************************");
    for (vector<pair<CLFormula, string>>::iterator it = mpT->mCLaxioms.begin();
         it != mpT->mCLaxioms.end(); it++) {
      stringstream ss;
      ss << "; " << it->first << endl;
      AddComment(ss.str());
    }

    for (unsigned i=0; i <= nFinalStep; i++) {
      Constraint cc, cg[2][2];
      for (unsigned ind0=0; ind0<2; ind0++)
        for (unsigned ind1=0; ind1<2; ind1++) {
          cg[ind0][ind1] = (ContentsPredicate(i,ind0) == ContentsPredicate(nFinalStep,ind1));
          for(unsigned int j = 0; j < mGoal.GetElement(ind1).GetElement(0).GetArity(); j++)
            cg[ind0][ind1] &= (ContentsArgument(i,ind0,j) == ContentsArgument(nFinalStep,ind1,j));
        }
      if (mGoal.GetSize() == 1) {
        cc =  ((Cases(i) == False()) & cg[0][0]);
      }
      else {
        cc =  ((Cases(i) == False()) & (cg[0][0] | cg[0][1])) |
               (Cases(i) & cg[0][0] & cg[1][1]);
      }
      AssertVar(IsGoal(i), cc);
    }

    AddComment("");
    AddComment("***************************** Premises ******************************");
    AddComment("");
    AddComment("****************************** Goal *********************************");

//    sPreabmle += "(assert " + mSMTout.appeq(mSMTout.app("nNesting", nFinalStep), 1) + ")\n";
    AssertVar(Cases(nFinalStep), formula.GetSize() > 1 ? True() : False());
    AssertVar(ContentsPredicate(nFinalStep, 0),
                  Constraint(ToUpper(formula.GetElement(0).GetElement(0).GetName())));

    for (size_t i = 0; i < formula.GetElement(0).GetElement(0).GetArity(); i++) {
      if (CONSTANTS.find(formula.GetElement(0).GetElement(0).GetArg(i)) == CONSTANTS.end())
        AssertVar(ContentsArgument(nFinalStep, 0, i),
                    Constraint(ToUpper(formula.GetElement(0).GetElement(0).GetArg(i))));
      else
        AssertVar(ContentsArgument(nFinalStep, 0, i),
                     Constraint(formula.GetElement(0).GetElement(0).GetArg(i)));
    }

    AddComment("");

  if (mSMT_theory == eSMTUFLIA_ProvingEngine ||
      mSMT_theory == eSMTUFBV_ProvingEngine) {
    mSMTfile << "(get-value (" << endl;
    for (set<string>::iterator it = GETVALUE.begin(); it != GETVALUE.end(); it++)
      if (it->find("bSameProofBranch") == string::npos &&
          it->find("bGoal") == string::npos &&
          it->find("bOddNesting") == string::npos &&
          it->find("bStepQED") == string::npos &&
          it->find("sbaMPStep") == string::npos)
        mSMTfile << *it << endl;
    mSMTfile << "))" << endl;
  }

  AssertVarBoolean(mConstraint & CorrectnessCondition());
  mSMTfile << "(check-sat)" << endl;
  mSMTfile << "(get-model)" << endl;
  mSMTfile.close();
}

// ---------------------------------------------------------------------------------------

bool NewSMTProvingEngine::ReadModel(const string &sModelFile)  {
  ifstream smtmodel(sModelFile, ios::in);
  if (!smtmodel.good())
    return false;
  if (smtmodel.peek() == std::ifstream::traits_type::eof()) // empty model
    return false;
  string str;
  if (!getline(smtmodel, str)) {
    cout << "Error in the model file!" << endl;
    return false;
  }
  if (str == "unsat" || str != "sat")
    return false;
  if (!getline(smtmodel, str)) {
    cout << "Error in the model file!" << endl;
    return false;
  }

  if (str.substr(0,strlen("(model")) != "(model" &&
          str.substr(0,strlen("(")) != "(")
    return false;
      // {if (!(mSMT_theory == eSMTUFLIA_ProvingEngine ||
      //       mSMT_theory == eSMTUFBV_ProvingEngine))
        // getline(smtmodel, str);
      // else
        // str = ""; }

  string strVarName, strVal;
  while (getline(smtmodel, strVarName) && getline(smtmodel, strVal)) {
    if (mSMT_theory == eSMTUFLIA_ProvingEngine ||
        mSMT_theory == eSMTUFBV_ProvingEngine) {
      str = str.substr(strlen(" (define-fun "), str.size());
    }
    else {
      strVarName = strVarName.substr(strlen("  (define-fun "), strVarName.size() - 1);
      strVarName = strVarName.substr(0, strVarName.find(' '));
      strVal = strVal.substr(strlen("    "), strVal.size());
      strVal = strVal.substr(0, strVal.find(')'));
      StoreValueFromModel(strVarName, strVal);
    }
  }
  return true;
}

// ---------------------------------------------------------------------------------------

bool NewSMTProvingEngine::StoreValueFromModel(string& strVarName, string& strVal)
{
  unsigned index[3], i = 0, nVal = 0;
  bool bVal = false;
  string s = strVarName;

  if (strVarName.substr(0,NUM_PREFIX.size()) == NUM_PREFIX)
    strVarName = strVarName.substr(NUM_PREFIX.size(),strVarName.size()); // strip prefix
  strVarName = strVarName.substr(0, strVarName.find("_l_")); // strip arguments

  while (s.find("_l_") != string::npos) { // collect arguments
    s = s.substr(s.find("_l_") + strlen("_l_"), s.size());
    if (!stou(s.substr(0,s.find("_r_")), index[i++]))
      return false;
    s = s.substr(s.find("_r_") + strlen("_r_"), s.size());
  }

  if (strVarName[0] == 'b') { // boolean
    bVal = (strVal == "true");
  }
  else {
    std::stringstream ss;
    ss << std::hex << strVal.substr(strlen("#x"),strVal.size());
    ss >> nVal;
  }

  if (strVarName == "StepKind") {
    meProof[index[0]].StepKind = nVal;
  } else if (strVarName == "ContentsPredicate") {
    meProof[index[0]].ContentsPredicate[index[1]] = nVal;
  } else if (strVarName == "ContentsArgument") {
    meProof[index[0]].ContentsArgument[index[1]][index[2]] = nVal;
  } else if (strVarName == "Nesting") {
    meProof[index[0]].Nesting = nVal;
  } else if (strVarName == "bisGoal") {
    meProof[index[0]].isGoal = bVal;
  } else if (strVarName == "AxiomApplied") {
    meProof[index[0]].AxiomApplied = nVal;
  } else if (strVarName == "From") {
    meProof[index[0]].From[index[1]] = nVal;
  } else if (strVarName == "Instantiation") {
    meProof[index[0]].Instantiation[index[1]] = nVal;
  } else if (strVarName == "bCases") {
    meProof[index[0]].Cases = bVal;
  }
  // else // constants and enums
  //  assert(false);
  return true;
}

// ---------------------------------------------------------------------------------------

bool NewSMTProvingEngine::ReconstructProof(const DNFFormula &formula,
                                            CLProof& proof)
{
    vector<Fact> proofTrace;
    msPredicates.resize(mpT->mSignature.size() + 1);
    int i = 0;
    for (size_t j = 0; j < mpT->mSignature.size(); j++)
      msPredicates[i++] = mpT->mSignature[j].first;
    i = 0;
    for (vector<string>::iterator it = mpT->mConstants.begin();
      it != mpT->mConstants.end(); it++)
    msConstants[i++] = *it;
    for (set<string>::iterator it = mpT->mConstantsPermissible.begin();
      it != mpT->mConstantsPermissible.end(); it++)
    msConstants[i++] = *it;
    unsigned start_step = 0;
    return ReconstructSubproof(formula, proof, start_step, proofTrace, false);
}

// ---------------------------------------------------------------------------------------

bool NewSMTProvingEngine::ReconstructSubproof(const DNFFormula &formula,
                                               CLProof& proof,
                                               unsigned& step,
                                               vector<Fact> &proofTrace, bool bNegIntro)
{
    Fact dummy;
    dummy.SetName("dummy");
    CaseSplit *pcs;

    for (; ; step++) { // ProofStep;
        unsigned nStepKind, nAxiom, nPredicate, nPredicate1, nBranching;
        nStepKind = meProof[step].StepKind;
        nAxiom = meProof[step].AxiomApplied;
        nPredicate = meProof[step].ContentsPredicate[0];
        nBranching = meProof[step].Cases;
        size_t numOfUnivVars = 0;
        size_t numOfExistVars = 0;
        if (nStepKind == eMP) {
          numOfUnivVars = mpT->mCLaxioms[nAxiom].first.GetNumOfUnivVars();
          numOfExistVars = mpT->mCLaxioms[nAxiom].first.GetNumOfExistVars();
        }
        for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate]); i++) {
          if (msConstants.find(meProof[step].ContentsArgument[0][i]) == msConstants.end()
              && numOfExistVars == 0) // eliminate spurious constants, also for inst[]
            meProof[step].ContentsArgument[i][i] = 0;
        }

        if (nStepKind == eQEDbyCases) {
          proof.SetProofEnd(pcs);
          proofTrace.push_back(dummy);
          return true;
        } else if (nStepKind == eQEDbyAssumption) {
          ByAssumption *pe = new ByAssumption(formula.GetElement(0));
          proof.SetProofEnd(pe);
          proofTrace.push_back(dummy);
          return true;
        } else if (nStepKind == eQEDbyEFQ) {
          EFQ *pe = new EFQ();
          proof.SetProofEnd(pe);
          proofTrace.push_back(dummy);
          return true;
        } /*else if (nStepKind == eQEDbyNegIntro) {
          proof.SetProofEnd(pni);
          proofTrace.push_back(dummy);
          return true;
        } */ else if (nStepKind == eAssumption) {
          Fact f;
          f.SetName(msPredicates[nPredicate]);
          for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate]); i++)
            f.SetArg(i, mpT->GetConstantName(meProof[step].ContentsArgument[0][i]));
          // proof.AddAssumption(f); // already added while reading theorem
          proofTrace.push_back(f);
        } else if (nStepKind == eFirstCase) {
          Fact f;
          f.SetName(msPredicates[nPredicate]);
          for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate]); i++)
            f.SetArg(i, mpT->GetConstantName(meProof[step].ContentsArgument[0][i]));
          proofTrace.push_back(f);
          CLProof subproof;
          subproof.SetTheory(mpT);
          subproof.AddAssumption(f); // add first case
          step++;
          if (!ReconstructSubproof(formula, subproof, step, proofTrace, false))
            return false;
          pcs->AddSubproof(subproof);
        } else if (nStepKind == eSecondCase) {
          Fact f;
          f.SetName(msPredicates[nPredicate]);
          for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate]); i++)
            f.SetArg(i, mpT->GetConstantName(meProof[step].ContentsArgument[0][i]));
          proofTrace.push_back(f);
          CLProof subproof;
          subproof.SetTheory(mpT);
          subproof.AddAssumption(f); // add second case
          step++;
          if (!ReconstructSubproof(formula, subproof, step, proofTrace, false))
            return false;
          pcs->AddSubproof(subproof);
        } else if (nStepKind == eMP) {
          if (nBranching) {
            nPredicate1 = meProof[step].ContentsPredicate[1];
            for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate1]); i++) {
              if (msConstants.find(meProof[step].ContentsArgument[1][i]) == msConstants.end() &&
                  numOfExistVars == 0)
                meProof[step].ContentsArgument[1][i] = 0; // eliminate spurious constants, also for inst[]
            }
          }
          ConjunctionFormula cfPremises;
          unsigned noPremises = mpT->mCLaxioms[nAxiom].first.GetPremises().GetSize();
          if (noPremises == 1 &&
              mpT->mCLaxioms[nAxiom].first.GetPremises().GetElement(1).GetName() == "true")
            noPremises = 0;
          size_t numOfVars = numOfUnivVars + numOfExistVars;
          for (unsigned int i = 0; i < noPremises; i++) {
            unsigned nFrom = meProof[step].From[i];
            if (nFrom != -1 && nFrom != 99 && nFrom != 98)
              cfPremises.Add(proofTrace[nFrom]);
            else
              if (nFrom == 98) {
                Fact univAxFact = mpT->mCLaxioms[nAxiom].first.GetPremises().GetElement(i);
              univAxFact.SetName("@" + univAxFact.GetName());
              cfPremises.Add(univAxFact);
            }
            else
              break;
          }
          int inst[numOfVars];
          for (size_t i = 0; i < numOfVars; i++) {
            inst[i] = meProof[step].Instantiation[i];
          }
          vector<pair<string, string>> instantiation;
          vector<pair<string, string>> new_witnesses;
          for (size_t i = 0; i < numOfUnivVars; i++) {
            string UnivVar = mpT->mCLaxioms[nAxiom].first.GetUnivVar(i);
            if (msConstants.find(inst[i]) == msConstants.end())
              inst[i] = 0; // eliminate spurious constants
            instantiation.push_back(
                pair<string, string>(UnivVar, msConstants[inst[i]]));
          }
          for (size_t i = 0; i < numOfExistVars; i++) {
            const string existVar = mpT->mCLaxioms[nAxiom].first.GetExistVar(i);
            const string newWitness = mpT->GetConstantName(inst[numOfUnivVars + i]);
            msConstants[inst[numOfUnivVars + i]] = newWitness;
            instantiation.push_back(pair<string, string>(existVar, newWitness));
            new_witnesses.push_back(pair<string, string>(existVar, newWitness));
          }

          Fact f;
          f.SetName(string(msPredicates[nPredicate]));
          for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate]); i++) {
            if (msConstants.find(meProof[step].ContentsArgument[0][i]) == msConstants.end())
              meProof[step].ContentsArgument[0][i] = 0; // eliminate spurious constants, also for inst[]
            f.SetArg(i, mpT->GetConstantName(meProof[step].ContentsArgument[0][i]));
          }

          DNFFormula d;
          ConjunctionFormula cfconc1, cfconc2;
          cfconc1.Add(f);
          d.Add(cfconc1);
          proofTrace.push_back(f); // this is not used if the axiom is branching

          if (nBranching) {
            Fact f;
            f.SetName(string(msPredicates[nPredicate1]));
            for (size_t i = 0; i < mpT->GetSymbolArity(msPredicates[nPredicate1]);
                 i++) {
              if (msConstants.find(meProof[step].ContentsArgument[1][i]) == msConstants.end())
                meProof[step].ContentsArgument[1][i] = 0; // eliminate spurious constants, also for inst[]
              f.SetArg(i, mpT->GetConstantName(meProof[step].ContentsArgument[1][i]));
            }
            cfconc2.Add(f);
            d.Add(cfconc2);

            pcs = new CaseSplit;
            vector<DNFFormula> vd;
            DNFFormula d1;
            d1.Add(cfconc1);
            DNFFormula d2;
            d2.Add(cfconc2);
            vd.push_back(d1);
            vd.push_back(d2);
            pcs->SetCases(vd);
          }

          // Instantiation of fact derived inline from univ axioms
          for (size_t ii = 0; ii < cfPremises.GetSize(); ii++) {
            if (cfPremises.GetElement(ii).GetName().at(0) == '@') {
              Fact univAxFact = cfPremises.GetElement(ii);
              for (size_t jj = 0; jj < univAxFact.GetArity(); jj++)
                for (size_t kk = 0; kk < instantiation.size(); kk++) {
                  if (univAxFact.GetArg(jj) == instantiation[kk].first)
                    univAxFact.SetArg(jj, instantiation[kk].second);
                }
              univAxFact.SetName(univAxFact.GetName().substr(1));
              cfPremises.SetElement(ii, univAxFact);
            }
          }
          string axiomName = mpT->mCLaxioms[nAxiom].second;
          proof.AddMPstep(cfPremises, d, axiomName, instantiation, new_witnesses);
          if (bNegIntro && mpT->GetSymbolArity(msPredicates[nPredicate]) == 0 &&
              !nBranching) { // false reached
            proof.SetProofEnd(NULL);
            return true;
          }
       }
    }
    return true;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::DeclareVarBasicType(const string& VarName)
{
  mSMTfile << "(declare-const " + VarName + " " + mSMT_type + " )" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::AssertVarBasicType(const string& VarName, unsigned u)
{
  mSMTfile << "(assert (= " + VarName + " #x" + itohexs(u) + "))" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::DeclareVarBoolean(const string& VarName)
{
  mSMTfile << "(declare-const " + VarName + " " + "Bool" + " )" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::AssertVarBoolean(const Constraint& c)
{
  mSMTfile << "(assert " + c.toSMT() + ")" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::AssertVarBoolean(const string& VarName)
{
  mSMTfile << "(assert " + VarName + ")" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::AssertVar(const string& VarName, const string& Val)
{
  mSMTfile << "(assert (= " + VarName + " " + Val + "))" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::AssertVar(const Constraint& c1, const Constraint& c2)
{
  mSMTfile << "(assert (= " + c1.toSMT() + " " + c2.toSMT() + "))" << endl;
}

// ----------------------------------------------------------

void NewSMTProvingEngine::AddComment(const string& comment)
{
  mSMTfile << "; " + comment << endl;
}

// ----------------------------------------------------------
