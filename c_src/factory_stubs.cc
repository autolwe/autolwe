#include <factory/factory.h>
#include <assert.h>
#include <algorithm>

using namespace std;

#define FOR0(i,n) for (i = 0; i < n; i++)

#define FOR1(i,n) for (i = 1; i <= n+1; i++)

/* --------------------------------------------------------------------- */
/* Create new array of exponent vectors.                                 */
/* --------------------------------------------------------------------- */
long** new_expvecs(int maxvar, int nterms) {
  long** evecs;
  int i, j;
  
  evecs = (long**) malloc(nterms * sizeof(long *));
  assert(evecs != NULL);
  FOR0(i, nterms) {
    evecs[i] = (long*) malloc(maxvar * sizeof(long));
    assert(evecs[i] != NULL);
    FOR0(j,maxvar) {
      evecs[i][j] = 0;
    }
  }
  return evecs;
}

/* --------------------------------------------------------------------- */
/* Free array of exponent vectors.                                       */
/* --------------------------------------------------------------------- */
void free_expvecs(long **evecs, int nterms) {
  int i;
  
  FOR0(i, nterms) {
    free(evecs[i]);
  }
  free(evecs);
}

/* --------------------------------------------------------------------- */
/* Create new array for coefficients.                                    */
/* --------------------------------------------------------------------- */
long* new_coeffs(int nterms) {
  long* coeffs;
  int i;
  coeffs = (long*) malloc(nterms * sizeof(long));
  FOR0(i,nterms) {
    coeffs[i] = 0;
  }
  assert(coeffs != NULL);
  return coeffs;
}

extern "C" {
  // we encode 0 using maxvar=0, nterms=0, expvecs=NULL, coeffs=NULL
  // otherwise expvecs is an array of size [nterms][maxvars]
  // and coeffs an array of size [nterms]
  typedef struct {
    int    maxvar;
    int    nterms;
    long** expvecs;
    long*  coeffs;
  } DistrPoly;

  // non-empty list of distributed polynomials
  struct DPolyList {
    DistrPoly* head;
    int head_aux; // auxilliary information used, e.g., returning factors
    struct DPolyList* tail;
  };

  typedef struct DPolyList Litem;

  DistrPoly*
  copy_DistrPoly(DistrPoly dp) {
    DistrPoly* res = (DistrPoly*) malloc(sizeof(DistrPoly));
    res->maxvar  = dp.maxvar;
    res->nterms  = dp.nterms;
    res->expvecs = dp.expvecs;
    res->coeffs  = dp.coeffs;

    return res;
  }

  void
  free_DistrPoly(DistrPoly* dp) {
    if (dp->nterms > 0) {
      free_expvecs(dp->expvecs, dp->nterms);
      free(dp->coeffs);
    }
    free(dp);
  }

  void
  free_DPolyList(struct DPolyList* dpl) {
    struct DPolyList* next;
    struct DPolyList* cur = dpl;
    while (cur != NULL) {
      free_DistrPoly(cur->head);
      next = cur->tail;
      free(cur);
      cur = next;
    }
  }
}

/* --------------------------------------------------------------------- */
/* Return number of terms interpreting f in ZZ[v_1,..,v_k].              */
/* --------------------------------------------------------------------- */
int getNumTerms(CanonicalForm f) {
  int tn = 0;
  int d = degree(f);
  if (d < 1) {
    return (f != 0?1:0);
  } else {
    for (int i = d; i >= 0; --i) {
      if (f[i] != 0) {
        tn += getNumTerms(f[i]);
      }
    }
    return tn;
  }
}

/* --------------------------------------------------------------------- */
/* Print distributed repr.                                               */
/* --------------------------------------------------------------------- */
#ifdef HAVE_IOSTREAM
void printDistr(int maxvar, int nterms, long** expvecs, long* coeffs) {
  int i,j;
  FOR0(i,nterms) {
    if (i != 0) cout << "+";
    cout << coeffs[i];
    FOR0(j, maxvar) {
      if (expvecs[i][j] > 0) {
        cout << "*" << "v_" << j+1;
        if (expvecs[i][j]!=1) {
          cout << "^" << expvecs[i][j];
        }
      }
    }
  }
  cout << endl;
}
#endif

/* --------------------------------------------------------------------- */
/* Convert canonical form to distributed repr. (coeffs + exp. vectors)   */
/* --------------------------------------------------------------------- */
void
cfToDistr_aux(CanonicalForm f, int maxvar, int* term_idx,
              long* cur_expvec, long** expvecs, long* coeffs) {
  int i;
  int deg = degree(f);
  int lev = (f.mvar().level() > 0?f.mvar().level():0);
  // cout << *term_idx << "," << lev << "," << deg << ": " << f << endl;

  if (deg < 1) {
    coeffs[*term_idx] = f.intval();
    FOR0(i,maxvar) {
      expvecs[*term_idx][i] = cur_expvec[i];
    }
    assert(CanonicalForm(f.intval()) == f);  // FIXME: use bignums
    *term_idx += 1;
  } else {
    assert(f.mvar().level() > 0);
    for(i = deg; i >=0; --i) {
      if (f[i] != 0) {
        // cout << "  deg " << i << " in v_" << lev << endl;
        cur_expvec[ f.mvar().level() - 1 ] = i;
        cfToDistr_aux(f[i], maxvar, term_idx, cur_expvec, expvecs, coeffs);
        cur_expvec[ f.mvar().level() - 1 ] = 0;
      }
    }
  }
}

DistrPoly
cfToDistr(CanonicalForm f) {
  int maxvar  = max(f.mvar().level(),1);
  int nterms = getNumTerms(f);

  if (f == 0) {
    DistrPoly res;
    res.maxvar  = 0;
    res.nterms  = 0;
    res.expvecs = NULL;
    res.coeffs  = NULL;
    return res;
  } else {
    long** expvecs    = new_expvecs(maxvar, nterms);
    long*  cur_expvec = new_coeffs(maxvar);
    long*  coeffs     = new_coeffs(nterms);
    int    term_idx   = 0;

    cfToDistr_aux(f, maxvar, &term_idx, cur_expvec, expvecs, coeffs);
    free(cur_expvec);

    // printDistr(maxvar,nterms,expvecs,coeffs);
    DistrPoly res;
    res.maxvar  = maxvar;
    res.nterms  = nterms;
    res.expvecs = expvecs;
    res.coeffs  = coeffs;
    return res;
  }

} 

/* --------------------------------------------------------------------- */
/* Convert distributed repr. (coeffs + exp. vectors) to canonical form   */
/* --------------------------------------------------------------------- */
CanonicalForm distrToCf(int maxvar, int nterms, long** expvecs, long* coeffs) {
  int i, j;
  CanonicalForm f(0);
  FOR0(i,nterms) {
    CanonicalForm t(coeffs[i]);
    FOR0(j, maxvar) {
      t *= power(Variable(j+1),expvecs[i][j]);
    }
    f += t;
  }
  return f;
}

extern "C" {
  /* --------------------------------------------------------------------- */
  /* C wrapper for printing.                                               */
  /* --------------------------------------------------------------------- */
  void
  wrap_print(int maxvar, int nterms, long** expvecs, long* coeffs) {
#ifdef HAVE_IOSTREAM
    printDistr(maxvar, nterms, expvecs, coeffs);
#endif
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for exponent vectors allocation.                            */
  /* --------------------------------------------------------------------- */
  long**
  wrap_new_expvecs(int maxvar, int nterms) {
    return new_expvecs(maxvar, nterms);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for freeing exponent vectors.                               */
  /* --------------------------------------------------------------------- */
  void
  wrap_free_expvecs(long** expvecs, int nterms) {
    free_expvecs(expvecs, nterms);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for coefficient list allocation.                            */
  /* --------------------------------------------------------------------- */
  long*
  wrap_new_coeffs(int nterms) {
    return new_coeffs(nterms);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for coefficient list allocation.                            */
  /* --------------------------------------------------------------------- */
  void
  wrap_free_coeffs(long* coeffs) {
    free(coeffs);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for gcd computation.                                        */
  /* --------------------------------------------------------------------- */
  DistrPoly
  wrap_gcd(int maxvar1, int nterms1, long** expvecs1, long* coeffs1,
           int maxvar2, int nterms2, long** expvecs2, long* coeffs2) {

    CanonicalForm g = distrToCf(maxvar1,nterms1,expvecs1,coeffs1);
    CanonicalForm f = distrToCf(maxvar2,nterms2,expvecs2,coeffs2);
    CanonicalForm h = gcd(g,f);

    return cfToDistr(h);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for gcd computation.                                        */
  /* --------------------------------------------------------------------- */
  struct DPolyList*
  wrap_gcd_div(int maxvar1, int nterms1, long** expvecs1, long* coeffs1,
               int maxvar2, int nterms2, long** expvecs2, long* coeffs2) {

    CanonicalForm g = distrToCf(maxvar1,nterms1,expvecs1,coeffs1);
    CanonicalForm f = distrToCf(maxvar2,nterms2,expvecs2,coeffs2);
    CanonicalForm h = gcd(g,f);
    CanonicalForm gg = g / h;
    CanonicalForm ff = f / h;

    DistrPoly dh   = cfToDistr(h);
    DistrPoly* dhp = copy_DistrPoly(dh);
    DistrPoly dg = cfToDistr(gg);
    DistrPoly* dgp = copy_DistrPoly(dg);
    DistrPoly df = cfToDistr(ff);
    DistrPoly* dfp = copy_DistrPoly(df);
    
    Litem* i3 = (Litem *) malloc(sizeof(Litem));
    i3->head = dfp;
    i3->tail = NULL;

    Litem* i2 = (Litem *) malloc(sizeof(Litem));
    i2->head = dgp;
    i2->tail = i3;
    
    Litem* i1 = (Litem *) malloc(sizeof(Litem));
    i1->head = dhp;
    i1->tail = i2;

    return i1;
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for polynomial remainder.                                   */
  /* --------------------------------------------------------------------- */
  DistrPoly
  wrap_reduce(int maxvar1, int nterms1, long** expvecs1, long* coeffs1,
              int maxvar2, int nterms2, long** expvecs2, long* coeffs2) {
    // cout << "div" << endl;

    CanonicalForm g = distrToCf(maxvar1,nterms1,expvecs1,coeffs1);
    CanonicalForm f = distrToCf(maxvar2,nterms2,expvecs2,coeffs2);
    CanonicalForm h = reduce(g,f);
    
    // cout << "reduce g " << g << endl;
    // cout << "reduce f " << f << endl;
    // cout << "reduce h " << h << endl;

    DistrPoly res = cfToDistr(h);
    // cout << "converted" << endl;
    return res;
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for polynomial remainder.                                   */
  /* --------------------------------------------------------------------- */
  int
  wrap_reduce_zero(int maxvar1, int nterms1, long** expvecs1, long* coeffs1,
                   int maxvar2, int nterms2, long** expvecs2, long* coeffs2) {

    CanonicalForm g = distrToCf(maxvar1,nterms1,expvecs1,coeffs1);
    CanonicalForm f = distrToCf(maxvar2,nterms2,expvecs2,coeffs2);
    //CanonicalForm h = reduce(g,f);

    // FIXME: debug why reduce is not working here:
    // reduce -v_2 v_1*v_2 = 0
    //
    // cout << "reduce_zero" << endl;
    // cout << "g: " << g << endl;
    // cout << "f: " << f << endl;
    // cout << "reduce f g: " << reduce(f,g) << endl;
    // cout << "reduce g f: " << reduce(g,f) << endl;
    // cout << "div g f: " << div(g,f) << endl;
    // cout << "gcd g f: " << gcd(g,f) << endl;

    // return (h == 0);

    CanonicalForm w = gcd(g,f);
    return (w == f || -w == f);
  }

  /* --------------------------------------------------------------------- */
  /* C wrapper for polynomial division.                                    */
  /* --------------------------------------------------------------------- */
  DistrPoly
  wrap_div(int maxvar1, int nterms1, long** expvecs1, long* coeffs1,
           int maxvar2, int nterms2, long** expvecs2, long* coeffs2) {
    CanonicalForm g = distrToCf(maxvar1,nterms1,expvecs1,coeffs1);
    CanonicalForm f = distrToCf(maxvar2,nterms2,expvecs2,coeffs2);
    CanonicalForm h = g / f;

    // cout << "div g " << g << endl;
    // cout << "div f " << f << endl;
    // cout << "div h " << h << endl;

    return cfToDistr(h);
  }
  /* --------------------------------------------------------------------- */
  /* C wrapper for factorization of polynomials.                           */
  /* FIXME: Seems to leak some memory, here or in OCaml wrapper.           */
  /* --------------------------------------------------------------------- */
  struct DPolyList*
  wrap_factor(int maxvar, int nterms, long** expvecs, long* coeffs) {
    CanonicalForm f = distrToCf(maxvar,nterms,expvecs,coeffs);
    CFFList F;
    CFFactor h;
    F = factorize( f );
    struct DPolyList * res = NULL;
    for ( ListIterator<CFFactor> i = F; i.hasItem(); ++i ) {
      h = i.getItem();
      //cout << h << endl;
      
      DistrPoly dh   = cfToDistr(h.factor());
      DistrPoly* dhp = copy_DistrPoly(dh);
      Litem* it = (Litem *) malloc(sizeof(Litem));
      it->head = dhp;
      it->head_aux = h.exp();
      it->tail = res;
      res = it;
    }
    return res;
  }
}

#ifdef WITHMAIN
int main() {
    setCharacteristic( 0 );
    On( SW_USE_EZGCD );
    // On( SW_RATIONAL );

    // Example for conversion from distributed form to recursive form by evaluation
    CanonicalForm g =
      CanonicalForm("2",10) * power(Variable(1),1) * power(Variable(2),2) * power(Variable(3),3);
    g += CanonicalForm("3",10) * power(Variable(1),3) * power(Variable(2),1) * power(Variable(3),2);
    g += CanonicalForm("4",10) * power(Variable(1),3) * power(Variable(2),7) * power(Variable(3),2);
    cout << "define cf g:  " << g << endl;

    // convert from CanonicalForm to OCaml interface repr.
    DistrPoly dg = cfToDistr(g);

    // print result
    cout << "distr g:      "; printDistr(dg.nterms,dg.maxvar,dg.expvecs,dg.coeffs);

    // convert from CanonicalForm to OCaml interface repr.
    cout << "back to cf g: " << distrToCf(dg.maxvar,dg.nterms,dg.expvecs,dg.coeffs) << endl;

    DistrPoly dc = cfToDistr(CanonicalForm(0));

    cout << "distr c:      "; printDistr(dc.nterms,dc.maxvar,dc.expvecs,dc.coeffs);

    // convert from CanonicalForm to OCaml interface repr.
    cout << "back to cf c: " << distrToCf(dc.maxvar,dc.nterms,dc.expvecs,dc.coeffs) << endl;
 
    
    CanonicalForm u = Variable(1) + 7;
    CanonicalForm v = Variable(3)*3 + Variable(2);
    CanonicalForm q = Variable(2)*Variable(2) + 6;
    CanonicalForm w = u*q + v;

    cout << "w: " << w << endl;
    cout << "reduce(w,u) == v: " << (reduce(w,u) == v) << endl;
    cout << "(w / u)*u + reduce(w,u) == w: "
         << ((w / u)*u + reduce (w,u) == w) << endl;
}
#endif
