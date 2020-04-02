/* O(1.6181^n)-time Monien-Speckenmeyer branching algorithm for k-sat */
/* Author: Ruijie Fang (ruijief@princeton.edu)                        */
/* Input format: Dimacs CNF                                           */
/* Input format reference:                                            */
/*  http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SATLINK____DIMACS */
/* Algorithm Reference: Exact Exponential Algorithms by D. Kratsch & F. V. Fomin, Ch 2.2, and Monien, B. and Speckenmeyer, E.: Solving satisfiability in less than 2^n steps, Discrete Appl. Math. 10 (1985), 287–295. */
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <vector>
using namespace std;

/* A clause is a vector of integers (literals). */
typedef vector<int> clause;

/* A handy structure for a CNF formula. */
struct CNF {
  /* n-variable, m-clauses k-CNF formula */
  int n; int m; int k;
  int* t; /* assignment table */
  vector<clause> f; /* formula, vector of clauses */
};

/* Copies the assignment table. */
int* CNF_copy_table(CNF& cnf)
{
  int *t = new int[cnf.n + 1];
  for(int i = 0; i <= cnf.n; ++i) t[i] = cnf.t[i];
  return t;
}

/* Swaps the assignment table of CNF with a new one. */
void CNF_swap_table(CNF& cnf, int *t)
{
  if (cnf.t) delete[] cnf.t;
  cnf.t = t;
}

/* is the m-th clause true in CNF */
int CNF_clause_true(CNF& cnf, int m)
{
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_clause_true: Access illegal clause %d in CNF with %d clauses.\n", m, cnf.m); return -1; }
  for(const int& i : cnf.f[m]) 
    /* if one literal in clause is true, then clause is true. */
    if ((i < 0 && cnf.t[-i] == 0) || (i > 0 && cnf.t[i] == 1)) return 1;
  return 0;
}

/* Is the m-th clause empty in CNF */
/* Basically, return 1 if and only if everything inside formula is set to false. */
int CNF_clause_false(CNF& cnf, int m)
{
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_clause_empty: Access illegal clause %d in CNF with %d clauses.\n", m, cnf.m); return -1; }
  for(const int& i : cnf.f[m]) 
    if (cnf.t[i] == -1 || cnf.t[i] == 1) return 0;
  return 0;
}

/* Is clause partial assignment */
int CNF_clause_partial(CNF& cnf, int m)
{
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_clause_partial: Access illegal clause %d in CNF with %d clauses.\n", m, cnf.m); return -1; }
  for(const int& i : cnf.f[m]) 
    if (cnf.t[i] == -1) return 1;
  return 0;
}

/* Associate literal l with value b in CNF */
int CNF_set(CNF& cnf, int l, int b) 
{
  if (l < 0) { l = -l; b = !b; }
  if (l > cnf.n) { fprintf(stderr, "CNF_set: Illegal literal is being set: %d\n", l); return -1; }
  if (!cnf.t) { fprintf(stderr, "CNF_set: Null CNF assignment table is being set.\n"); return -1; }
  cnf.t[l] = b;
  return 0;
}

/* Is a CNF evaluate to true. */
int CNF_ok(CNF& cnf) 
{
  int ok = 1;
  for(size_t i = 0; i < cnf.f.size(); ++i)
    ok = ok && CNF_clause_true(cnf, i);
  return ok;
}

/* Does a CNF contain an empty clause. */
int CNF_contains_false_clause(CNF& cnf)
{
  for(size_t i = 0; i < cnf.f.size(); ++i) 
    if (CNF_clause_false(cnf, i)) return 1;
  return 0;
}

/* Sets the literals in prefix [0...i-1] clause m in CNF to be false. */
int CNF_clause_zero_prefix_until(CNF& cnf, size_t m, size_t i)
{
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_clause_zero_prefix: Illegal clause %lu in CNF instance of %lu clauses\n", m, cnf.f.size()); return -1; }
  if (i > cnf.f[m].size()) { fprintf(stderr, "CNF_clause_zero_prefix: Illegal prefix %lu in CNF clause of %lu literals\n", i, cnf.f[m].size()); return -1; }
  size_t c = 0;
  for(const int& lit : cnf.f[m]) {
    int x = lit;
    if (x < 0) x = -x;
    if (cnf.t[x] == -1) {
      if (c < i) {
        CNF_set(cnf, lit, 0); /* Set literal, not variable! */ 
      } else if (c == i) { /* Reached i-th idx. bail out */
        CNF_set(cnf, lit, 1); 
        return 0;
      }
      ++c;
    }
  }
  return 0;
}

/* size of m-th clause */
size_t CNF_size_of_clause(CNF& cnf, size_t m)
{
  size_t sz = 0;
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_size_of_clause: Illegaal clause %lu in CNF instance of %lu clauses\n", m, cnf.f.size()); return -1;  }
  if (CNF_clause_false(cnf, m)) return 0;
  if (CNF_clause_true(cnf, m)) return 0;
  for(const int &i : cnf.f[m]) 
    if (i < 0) {
      if (cnf.t[-i] == -1) ++sz;
    } else {
      if (cnf.t[i] == -1) ++sz;
    }
  return sz;
}
  
/* Returns the index of the clause of minimum size inside a non-empty CNF. */
size_t CNF_clause_of_min_size(CNF& cnf)
{
  size_t winner = 0, winner_size = 0xfffffff;
  for(size_t i = 0; i < cnf.f.size(); ++i) {
    size_t sz = CNF_size_of_clause(cnf, i);
    if (CNF_clause_partial(cnf, i) && sz <= winner_size) {
      winner = i; winner_size = sz;
    }
  }
  return winner;
}

void print_table(CNF& cnf)
{
  printf("SATSolver Status ----------------\n");
  printf("> NVars=%d, NClauses=%d, k=%d\n", cnf.n, cnf.m, cnf.k);
  printf("> Assignment table: \n");
  for(int i = 1; i <= cnf.n; ++i) 
    printf("> * Var %d -> %d\n", i, cnf.t[i]);
  printf("> CNF: \n");
  for(size_t i = 0; i < cnf.f.size(); ++i) {
    printf("> * F[%lu]: ", i); 
    for(const int& l : cnf.f[i]) {
      if (l < 0) {
        if (cnf.t[-l] == 1) printf("| !x%d=0 ", -l);
        if (cnf.t[-l] == 0) printf("| !x%d=1 ", -l);
        if (cnf.t[-l] == -1) printf("| !x%d ", -l);
      } else {
        if (cnf.t[l] == 1) printf("| x%d=1 ", l);
        if (cnf.t[l] == 0) printf("| x%d=0 ", l);
        if (cnf.t[l] == -1) printf("| x%d ", l);
      }
    }
    printf("\n");
  }
  printf("---------------------------------\n");
}

/* O(1.9660)-time algorithm, without the need to detect autarkies. */
int k_sat1(CNF& cnf)
{
  int ok = 0; 
  size_t min_idx;
  print_table(cnf);
  /* If empty formula then true. */
  if (CNF_ok(cnf)) return 1;
  /* If cnf has empty clause then false. */
  if (CNF_contains_false_clause(cnf)) return 0;
  /* Copy assignment table. */
  /* Choose a clause of minimum size. It really could be any clause here,
   * but for consistency with k_sat2, we choose a clause of minimum size. */
  min_idx = CNF_clause_of_min_size(cnf);
  printf("k_sat1: Chosen clause at index %lu\n", min_idx);
  for(size_t i = 0; i < CNF_size_of_clause(cnf, min_idx); ++i) {
    int * t = CNF_copy_table(cnf);
    CNF_clause_zero_prefix_until(cnf, min_idx, i);
    ok = ok || k_sat1(cnf);
    CNF_swap_table(cnf, t);
  }
  return ok;
}

int main(int argc, char ** argv)
{
  CNF cnf; // CNF with n variables, m clauses 
  cnf.n = atoi(argv[1]);
  cnf.m = atoi(argv[2]);
  cnf.k = atoi(argv[3]);
  for(int i = 0; i < cnf.n; ++i) {
    printf("%d-th clause: ", i); 
    cnf.f.push_back(vector<int>());
    for(int j = 0; j < cnf.k; ++j) { 
      int x = atoi(argv[4 + i * cnf.k + j]);
      cnf.f[i].push_back(x);
      printf("%d ", x);
    }
    printf("\n");
  }
  cnf.t = new int[cnf.n + 1];
  for(int i = 0; i <= cnf.n; ++i) cnf.t[i] = -1;
  printf("is satisfiable: %d\n", k_sat1(cnf));
  return 0;
}

