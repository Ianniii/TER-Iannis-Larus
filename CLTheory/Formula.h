#ifndef FORMULA_H
#define FORMULA_H
#define NATIVE_EQ 1
#define NATIVE_NEG 1

#include <string>
#include <vector>
#include <set>
#include <map>
#include <iostream>
#include "common.h"
// #include "Theory/theory.h"

using namespace std;

class ProvingEngine;
class Theory;

// ---------------------------------------------------------------------------------------
class Fact
{
public:
    Fact() { }
    Fact(string& n, const vector<string>& a) { mName = n; mArgs = a; }
    Fact (const Fact &f) { mName = f.mName; mArgs = f.mArgs; }
    Fact& operator=(const Fact& f) { mName = f.mName; mArgs = f.mArgs; return *this; }
    Fact (const string& s);
    size_t GetArity() const { return mArgs.size(); }
    string GetArg(size_t i) const { return (mArgs.size()>i ? mArgs[i] : "null"); }
    string GetName() const { return mName; }
    void SetName(const string& name) { mName = name; }
    bool Read(const string& s);
    void SetArg(size_t i, const string& s) {
        if (mArgs.size() <= i)
            mArgs.resize(i+1);
        mArgs[i]=s;
    }
    bool Equals(const Fact& f) const;

    bool operator<(const Fact &rhs) const {

        if (GetName() < rhs.GetName())
            return 1;
        if (GetName() > rhs.GetName())
            return 0;
        size_t lsize = GetArity();
        size_t rsize = rhs.GetArity();
        if (lsize < rsize)
            return 1;
        if (lsize > rsize)
            return 0;
        for (size_t i = 0; i != lsize; i++) {
            if (GetArg(i) < rhs.GetArg(i))
                return 1;
            if (GetArg(i) > rhs.GetArg(i))
                return 0;
        }
        return 0;
        }

private:
    string mName;
    vector<string> mArgs;
};


// ---------------------------------------------------------------------------------------

class ConjunctionFormula
{
public:
    ConjunctionFormula() {}
    ConjunctionFormula(const ConjunctionFormula &cf) { mConjunction = cf.mConjunction; }
    ConjunctionFormula& operator=(const ConjunctionFormula& cf) { mConjunction = cf.mConjunction; return *this; }
    ConjunctionFormula(vector<Fact>& cf) { mConjunction = cf; }
    size_t GetSize() const { return mConjunction.size(); }
    Fact GetElement(size_t i) const { return (mConjunction.size()>i ? mConjunction[i] : mConjunction[0]); }
    void Add(const Fact& f) { mConjunction.push_back(f); }
    void SetElement(size_t i, const Fact& f) { mConjunction[i]=f; }
    bool Read(const string& s);
    void Clear() { mConjunction.clear(); }
    static bool less (const ConjunctionFormula& lhs, const ConjunctionFormula& rhs);
    const vector<Fact>& GetConjunction() const { return mConjunction; }
    bool Equals(const ConjunctionFormula& f) const;
    bool UsesNativeEq() const;

private:
    vector<Fact> mConjunction;
};


// ---------------------------------------------------------------------------------------

class DNFFormula

{
public:
    DNFFormula() {}
    DNFFormula(vector<ConjunctionFormula> dnf) { mDNF = dnf; }
    size_t GetSize() const { return mDNF.size(); }
    const ConjunctionFormula& GetElement(size_t i) const { return (mDNF.size()>i ? mDNF[i] : mDNF[0]); }
    void Add(const ConjunctionFormula& cf) { mDNF.push_back(cf); }
    void SetElement(size_t i, const ConjunctionFormula& cf) { mDNF[i]=cf; }
    bool Read(const string& s);
    const vector<ConjunctionFormula>* GetDNF() const { return &mDNF; }
    bool Equals(const DNFFormula& f) const;
    void Clear() { mDNF.clear(); }

private:
    bool MatchingBrackets(const string& v) const;

    vector<ConjunctionFormula> mDNF; // fixme
};

// ---------------------------------------------------------------------------------------

class CLFormula
{
public:
    CLFormula()  {  }
    CLFormula(const ConjunctionFormula& a, const DNFFormula& b)  { mA=a; mB=b; }
    friend ostream& operator<<(ostream& os, const CLFormula& f);
    const ConjunctionFormula& GetPremises() const { return mA; }
    const DNFFormula& GetGoal() const { return mB; }
    bool Read(const string& s);
    bool ReadImplication(const string& v, ConjunctionFormula& A, DNFFormula& B);
    bool MatchingBrackets(const string& v) const;

    size_t GetNumOfUnivVars() const { return mUniversalVars.size(); }
    const string& GetUnivVar(size_t i) const { return mUniversalVars[i]; }
    size_t GetNumOfExistVars() const { return mExistentialVars.size(); }
    const string& GetExistVar(size_t i) const { return mExistentialVars[i]; }

    void AddUnivVar(const string& varName) { mUniversalVars.push_back(varName); }
    void AddExistVar(const string& varName) { mExistentialVars.push_back(varName); }

    int UnivVarOrdinalNumber(string v) const;
    int ExistVarOrdinalNumber(string v) const;

    void ClearUnivVars() { mUniversalVars.clear(); }
    void ClearExistVars() {  mExistentialVars.clear(); }

    void Normalize(const string& name, const string& suffix, vector< pair<CLFormula,string> >& output) const;
    void NormalizeGoal(const string& name, const string& suffix, vector< pair<CLFormula,string> >& output) const;
    static Fact MergeFacts(const string& suffix, const Fact a, const Fact b);

    bool UsesNativeEq() const;

    void Clear() { mA.Clear(); mB.Clear(); ClearUnivVars(); ClearExistVars(); }

private:
    ConjunctionFormula mA;
    DNFFormula mB;

    vector<string> mUniversalVars;
    vector<string> mExistentialVars;

};


// ---------------------------------------------------------------------------------------
inline ostream& operator<<(ostream& os, const Fact& f)
{
    if (f.GetName() == "false") {
        os << "$false";
    }
    else if (f.GetName() == "true") {
        os << "$true";
    }
    else if (f.GetName() == EQ_NATIVE_NAME)
    {
        os  << "( " << f.GetArg(0) << " = " << f.GetArg(1) << " )";
    }
    else if (f.GetName() == PREFIX_NEGATED+EQ_NATIVE_NAME)
    {
        os << "( " << f.GetArg(0) << " != " << f.GetArg(1) << " )";
    }
    else
    {
        if (f.GetName()[0]=='n')
        {
            os << "~ (" << f.GetName().substr(1) << ")" ;
        }
        else
        {
           os << f.GetName();
        }
        if (f.GetArity() > 0) {
            os << "(";
            for (size_t i = 0; i < f.GetArity(); i++) {
                os << f.GetArg(i);
                if (i != f.GetArity()-1)
                    os << ",";
            }
            if (f.GetName()[0]=='n')
                os << ")";
            os << ")";
        }         
    }
    return os;
}

// ---------------------------------------------------------------------------------------
inline ostream& operator<<(ostream& os, const ConjunctionFormula& f)
{
    os << "(";
    for (size_t i = 0; i < f.GetSize(); i++) {
        os << f.GetElement(i);
        if (i != f.GetSize()-1)
            os << " & ";
    }
    os << ")";
    return os;
}

// ---------------------------------------------------------------------------------------
inline ostream& operator<<(ostream& os, const DNFFormula& f)
{
    os << "(";
    for (size_t i = 0; i < f.GetSize(); i++) {
        os << f.GetElement(i);
        if (i != f.GetSize()-1)
           os << " | ";
    }
    os << ")";
    return os;
}

// ---------------------------------------------------------------------------------------
inline ostream& operator<<(ostream& os, const CLFormula& f)
{
    size_t size = f.GetNumOfUnivVars();
    if (size > 0) {
        os << "(! [";
        for (size_t i = 0; i < size; i++) {
            os << f.GetUnivVar(i);
            if (i+1 < size)
               os << ",";
        }
        os << "] : ";
    }
    size = f.GetNumOfExistVars();
    if (size > 0) {
        os << "(? [";
        for (size_t i = 0; i < size; i++) {
            os << f.GetExistVar(i);
            if (i+1 < size)
               os << ",";
        }
        os << "] : ";
    }
    if (f.mA.GetSize() >0)
    {
        os << "(" << f.mA << " => " << f.mB << ")";
    }
    else
    {
        os <<  f.mB;   
    }
    
    if (f.mUniversalVars.size() > 0)
        os << ")";
    if (f.mExistentialVars.size() > 0)
        os << ")";

    // os << endl;
    return os;
}

// ---------------------------------------------------------------------------------------

string SkipChar(const string& str, char c);
string ToUpper(const string& str);
bool ReadTPTPStatement(const string s, CLFormula& cl, string& axname, size_t& type);
bool ReadSetOfTPTPStatements(Theory *pT, const vector<string>& statements);

// ---------------------------------------------------------------------------------------


#endif // FORMULA_H
