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
typedef clause vector<int>;

/* A handy structure for a CNF formula. */
struct CNF {
  /* n-variable, m-clauses k-CNF formula */
  int n; int m; int k;
  int* t; /* assignment table */
  vector<clause> f; /* formula, vector of clauses */
}

/* Initializes given CNF instance. */
void CNF_init(CNF& cnf)
{
  if (cnf.t!=NULL) {
    for(size_t i = 0; i < n; ++i) t[i] = -1;
  }
}

/* Copies the assignment table. */
int* CNF_copy_table(CNF& cnf)
{
  int *t = new int[cnf.n];
  for(int i = 0; i < n; ++i) t[i] = cnf.t[i];
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
    if ((i < 0 && !cnf.t[-i]) || (i > 0 cnf.t[i])) return 1;
  return 0;
}

/* Is the m-th clause empty in CNF */
int CNF_clause_empty(CNF& cnf, int m)
{
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_clause_empty: Access illegal clause %d in CNF with %d clauses.\n", m, cnf.m); return -1; }
  for(const int& i : cnf.f[m]) if (cnf.t[i] == -1) return 1;
  return 0;
}

/* Associate literal l with value b in CNF */
int CNF_set(CNF& cnf, int l, int b) 
{
  if (l < 0) { l = -l; b = !b; }
  if (l >= n) { fprintf(stderr, "CNF_set: Illegal literal is being set: %d\n", l); return -1; }
  if (!cnf.t) { fprintf(stderr, "CNF_set: Null CNF assignment table is being set.\n"); return -1; }
  cnf->t[l] = b;
  return 0;
}

/* Is a CNF evaluate to true. */
int CNF_ok(CNF& cnf) 
{
  int ok = 0;
  for(size_t i = 0; i < f.size(); ++i) ok = ok && CNF_clause_true(cnf, i);
  return ok;
}

/* Does a CNF contain an empty clause. */
int CNF_contains_empty_clause(CNF& cnf)
{
  for(size_t i = 0; i < cnf.f.size(); ++i) if (CNF_clause_empty(cnf, i)) return 1;
  return 0;
}

/* Is the CNF formula empty. */
int CNF_formula_empty(CNF& cnf)
{
  return CNF_contains_empty_clause(cnf);
}

/* Sets the literals in prefix [0...i-1] clause m in CNF to be false. */
int CNF_clause_zero_prefix(CNF& cnf, size_t m, size_t i)
{
  if (m >= cnf.f.size()) { fprintf(stderr, "CNF_clause_zero_prefix: Illegal clause %lu in CNF instance of %lu clauses\n", m, cnf.f.size()); return -1; }
  if (i > cnf.f[m].size()) { fprintf(stderr, "CNF_clause_zero_prefix: Illegal prefix %lu in CNF clause of %lu literals\n", i, cnf.f[m].size()); return -1; }
  for(size_t j = 0; j < i; ++j) {
    CNF_set(cnf, cnf.f[m][j], 0);
  }
  return 0;
}

/* Returns the index of the clause of minimum size inside a non-empty CNF. */
size_t CNF_clause_of_min_size(CNF& cnf)
{
  size_t winner = 0, winner_size = 0xfffffff;
  for(size_t i = 0; i < cnf.f.size(); ++i) 
    if (cnf.f[i].size() <= winner_size) {
      winner = i; winner_size = cnf.f[i].size();
    }
  return winner;
}

/* Is a subformula F' \subseteq F an autark set. Compares a new table against the old. */
int CNF_is_autark(CNF& f, int* new_t)
{
  if (new_t == NULL || f.t == NULL) { fprintf(stderr, "CNF_is_autark: assignment table is NULL\n"); return -1; }
  l
}

/* O(1.9660)-time algorithm, without the need to detect autarkies. */
int k_sat1(CNF& cnf)
{
  int ok = 0; 
  size_t min_idx;
  /* If empty formula then true. */
  if (cnf.f.size() == 0) return 1;
  /* If cnf has empty clause then false. */
  if (CNF_empty_clause(cnf)) return 0;
  /* Copy assignment table. */
  /* Choose a clause of minimum size. It really could be any clause here,
   * but for consistency with k_sat2, we choose a clause of minimum size. */
  min_idx = CNF_clause_of_min_size(cnf);
  /* Make a backup of current assignment table. */
  int *t = CNF_copy_table(cnf);
  for(size_t i = 0; i < cnf.f[min_idx].size(); ++i) {
    CNF_clause_zero_prefix(cnf, min_idx, i);
    CNF_set(cnf, cnf.f[m][i], 1);
    ok = ok || k_sat1(cnf);
  }
  /* Restore the old assignment table. */
  CNF_swap_table(cnf, t);
  return ok;
}

/* The algorithm. */
int k_sat2(CNF& cnf)
{
  size_t min_idx;
  /* If empty formula then true. */
  if (cnf.f.size() == 0) return 1; 
  /* If cnf has empty clause then false. */
  if (CNF_empty_clause(cnf)) return 0;
  /* Choose a clause of minimum size. */
  min_idx = CNF_clause_of_min_size(cnf);
  /* todo */
  return 0;
}



