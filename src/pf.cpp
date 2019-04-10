#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "asa241.h"
#include "pf.h"

double PF::log_fact(double n) {
    return lgamma(n + 1);
}

/* This algorithm is constant time, but it doesn't work well when n >>
 k, because then log_fact(n) and log_fact(n - k) are too close
 together */
double PF::log_choose_gamma(double n, double k) {
    return (log_fact(n) - log_fact(n - k)) - log_fact(k);
}

/* When n >> k, n!/(n-k)! is almost n^k, which suggests the following
 refinement of log_choose_gamma. However some more thought is
 probably needed about how to choose between the two formulas. */
double PF::log_choose_gamma2(double n, double k) {
    if (n / k > 1000000000) {
        return log(n)*k - log_fact(k);
    } else {
        return (log_fact(n) - log_fact(n - k)) - log_fact(k);
    }
}

/* This algorithm takes O(k) steps, but as long as k is small, it
 gives good results even for very large n.
 */
double PF::log_choose_small_k(double n, int k) {
    double l = 0;
    int i;
    for (i = 0; i < k; i++) {
        l += log(n - i);
        l -= log(k - i);
    }
    return l;
}

void PF::normalize(struct Particles ary[], int nSamples) {
    int i;
    double total = 0, new_total = 0;
    for (i = 0; i < nSamples; i++) {
        assert(ary[i].weight >= 0);
        total += ary[i].weight;
    }
    assert(total > 0);
    for (i = 0; i < nSamples; i++) {
        ary[i].weight = ary[i].weight / total;
        assert(ary[i].weight >= 0 && ary[i].weight <= 1.0);
        new_total += ary[i].weight;
    }
    assert(new_total >= 0.999 && new_total <= 1.001);
}

void PF::normalize_cdf(double ary[], int nSamples) {
    int i;
    double total = 0, new_total = 0;
    for (i = 0; i <= nSamples; i++) {
        assert(ary[i] >= 0);
        total += ary[i];
    }
    assert(total > 0);
    for (i = 0; i <= nSamples; i++) {
        ary[i] = ary[i] / total;
        assert(ary[i] >= 0 && ary[i] <= 1.0);
        new_total += ary[i];
    }
    assert(new_total >= 0.999 && new_total <= 1.001);
}

double PF::mean_pdf(struct Particles ary[], int nSamples) {
    int i;
    double total = 0;
    for (i = 0; i < nSamples; i++) {
        total += ary[i].influence*ary[i].weight;
    }
    return total;
}

double PF::variance_pdf(struct Particles ary[], int nSamples) {
    int i;
    double total_x = 0, total_xx = 0;
    for (i = 0; i < nSamples; i++) {
        total_x += ary[i].influence*ary[i].weight;
        total_xx += ary[i].influence*ary[i].influence*ary[i].weight;
    }
    return total_xx - total_x*total_x;
}

double PF::stddev_pdf(struct Particles ary[], int nSamples) {
    return sqrt(variance_pdf(ary, nSamples));
}

double PF::mean_particle(struct Particles ary[], int nSamples) {
    int i;
    double total = 0;
    for (i = 0; i < nSamples; i++) {
        total += ary[i].influence;
    }
    return total/nSamples;
}

double PF::variance_particle(struct Particles ary[], int nSamples) {
    int i;
    double total_x = 0, total_xx = 0;
    for (i = 0; i < nSamples; i++) {
        total_x += ary[i].influence;
        total_xx += ary[i].influence*ary[i].influence;
    }
    return total_xx/nSamples - total_x*total_x/nSamples/nSamples;
}

double PF::stddev_particle(struct Particles ary[], int nSamples) {
    return sqrt(variance_particle(ary, nSamples));
}

void PF::get_uniform_prior (struct Particles ary[], int nVars, int nSamples) {
    int i;
    for (i = 0; i < nSamples; i++) {
        ary[i].influence = (double)(nVars*i)/nSamples;
        ary[i].weight = 1.0;
    }
}

void PF::set_equal_weight (struct Particles ary[], int nSamples) {
    int i;
    for (i = 0; i < nSamples; i++) {
        ary[i].weight = 1.0;
    }
}

double PF::prob_eq_n(double bt, int k, int n) {
    double s = floor(pow(2.0, bt) + 0.5);
    double log_p1, log_p2, log_p, p;
    if (n > s)
        return 0; 
    log_p1 = -k * log(2);
    if (k == 0) {
        p = (s == n) ? 1.0 : 0.0;
    } else {
        log_p2 = log1p(-pow(2.0, -k));
        log_p = log_choose(s, n) + log_p1 * n + log_p2 * (s - n);
        p = exp(log_p);
    }
    if (p < 0.0) {
        fprintf(stderr, "Bug: negative probability\n");
        exit(1);
    } else if (p > 1.0) {
        fprintf(stderr, "Bug: probability more than 1.0\n");
        fprintf(stderr, "bt = %g, k = %d, n = %d, s = %g\n",
                bt, k, n, s);
        fprintf(stderr, "p = %g\n", p);
        if (n == 1) {
            fprintf(stderr, "log_choose = %g, s/b %g\n",
                    log_choose(s, n), log(s));
        }
        exit(1);
    }
    assert(p >= 0.0 && p <= 1.0);
    return p;
}

double PF::prob_ge_n(double bt, int k, int n) {
    int n2;
    double prob = 0.0;
    for (n2 = 0; n2 < n; n2++) {
        prob += prob_eq_n(bt, k, n2);
    }
    assert(prob >= -0.0001 && prob <= 1.0001);
    if (prob < 0)
        prob = 0.0;
    if (prob > 1)
        prob = 1.0;
    return 1.0 - prob;
}

void PF::estimate_posterior_eq_n(int k, int n, struct Particles a[], int nSamples) {
    int bt;
    for (bt = 1; bt < nSamples; bt++) {
        double p = a[bt].weight*prob_eq_n(a[bt].influence, k, n);
        a[bt].weight = p;
    }
    a[0].weight = a[1].weight;
    a[0].influence = 0;
    normalize(a, nSamples);
}

void PF::estimate_posterior_ge_n(int k, int n, struct Particles a[], int nSamples) {
    int bt;
    for (bt = 1; bt < nSamples; bt++) {
        double p = a[bt].weight*prob_ge_n(a[bt].influence, k, n);
        a[bt].weight = p;
    }
    a[0].weight = a[1].weight;
    a[0].influence = 0;
    normalize(a, nSamples);
}

int cmpfunc (const void * a, const void * b)
{
    struct Particles *p1 = (struct Particles *)a;
    struct Particles *p2 = (struct Particles *)b;
    if ( p1->influence > p2->influence) return 1;
    else if ( p1->influence < p2->influence) return -1;
    else return 0;
}

double PF::linear_intep (double a, double b, double w1, double w2) {
    return (b*w1+a*w2)/(w1+w2);
}

double* PF::get_cdf (struct Particles a[], int nSamples) {
    int i;
    double* res = new double[nSamples+1];
    for (i = 0; i <= nSamples; i++) {
        if(i == 0 ) {
            res[i] = a[i].weight/2;
        } else if (i == nSamples) {
            res[i] = a[i-1].weight/2;
        } else {
            res[i] = (a[i-1].weight+a[i].weight)/2;
        }
    }
    normalize_cdf(res, nSamples);
    return res;
}
void PF::sampling(struct Particles a[], struct Particles b[], int nVars, int nSamples) {
    double* cdf = new double[nSamples+1];
    cdf = get_cdf(a, nSamples);
    int i;
    for (i = 0; i < nSamples; i++) {
        double r1 = (double)rand() / (double)RAND_MAX;
        int index = 0;
        while (r1 > 0 && index < nSamples+1) {
            r1 = r1 - cdf[index];
            index++;
        }
        index--;
        double hi, lo;
        if (fabs(r1 + cdf[index]) > fabs(r1)) {
            hi = fabs(r1 + cdf[index]);
            lo = fabs(r1);
        } else {
            lo = fabs(r1 + cdf[index]);
            hi = fabs(r1);
        }
        if (index == 0) {
            b[i].influence = linear_intep(0, a[index].influence, lo, hi);
        } else if (index == nSamples + 1) {
            b[i].influence = linear_intep(a[index].influence, nVars, lo, hi);
        } else {
            if ( a[index-1].weight > a[index].weight) {
                b[i].influence = linear_intep(a[index-1].influence, a[index].influence, hi, lo);
            } else {
                b[i].influence = linear_intep(a[index-1].influence, a[index].influence, lo, hi);
            }
        }
    }
    
    qsort(b, nSamples, sizeof(struct Particles), cmpfunc);
    //normalize(b, NUM_SAMPLES);
    set_equal_weight(b, nSamples);
    delete [] cdf;
}

void load_particles(struct Particles a[], struct Particles b[], int nSamples) {
    for (int i = 0; i < nSamples; i++) {
        b[i].influence = a[i].influence;
        b[i].weight = a[i].weight;
    }
}

double PF::sum_weight(struct Particles ary[], int min, int max) {
    double sum = 0;
    int i;
    assert(min <= max);
    for (i = min; i <= max; i++) {
        sum += ary[i].weight;
    }
    if (sum < 0 || sum >= 1.01) {
        for (i = 0; i <= NUM_SAMPLES; i++) {
            printf ("%f ", ary[i].weight);
        }
        putchar('\n');
        printf ("%d %d error sum: %f\n",min, max, sum);
    }
    assert(sum >= 0 && sum < 1.01);
    return sum;
}

double PF::sum_pdf(struct Particles ary[], int min, int max, int nSamples) {
    double sum = 0;
    int i;
    double* cdf = new double[nSamples+1];
    cdf = get_cdf(ary, nSamples);
    assert(min <= max);
    for (i = min; i <= max; i++) {
        sum += cdf[i];
    }
    if (sum < 0 || sum >= 1.01) {
        for (i = 0; i <= nSamples; i++) {
            printf ("%f ", cdf[i]);
        }
        putchar('\n');
        printf ("%d %d error sum: %f\n",min, max, sum);
    }
    assert(sum >= 0 && sum < 1.01);
    return sum;
}

int PF::get_center_index(struct Particles ary[], int nSamples, double value)
{
    int res = 0;
    int i;
    for (i = 0 ; i < nSamples; i++) {
        if(value < ary[i].influence) {
            res = i;
            break;
        }
    }
    return res;
}

double PF::get_lb(struct Particles ary[], int cen, int nSamples, double confidence) {
    double res;
    double* cdf = get_cdf(ary, nSamples);
    double p = confidence + 0.5 * cdf[cen];
    while (p > 0 && cen > -1) {
        p = p - cdf[cen];
        cen--;
    }
    cen++;
    //printf("Lower Index is %d\n", cen);
    res = linear_intep(ary[cen].influence, ary[cen+1].influence, fabs(p), fabs(p + cdf[cen]));
    return res;
}

double PF::get_ub(struct Particles ary[], int cen, int nSamples, double confidence) {
    double res;
    double* cdf = get_cdf(ary, nSamples);
    double p = confidence + 0.5 * cdf[cen];
    while (p > 0 && cen < NUM_SAMPLES) {
        p = p - cdf[cen];
        cen++;
    }
    cen--;
    //printf("Upper Index is %d\n", cen);
    res = linear_intep(ary[cen-1].influence, ary[cen].influence, fabs(p), fabs(p + cdf[cen]));
    return res;
}

void PF::print_inf(struct Particles ary[], int nSamples) {
    int i;
    for (i = 0 ; i < nSamples; i++) {
        printf ("%f ", ary[i].influence);
    }
    printf ("\n");
}

void PF::print_weight(struct Particles ary[], int nSamples) {
    int i;
    for (i = 0 ; i < nSamples; i++) {
        printf ("%f ", ary[i].weight);
    }
    printf ("\n");
}

void PF::gnuplot_data(const char *fname, struct Particles ary[], int size) {
    int i;
    int res;
    FILE *fp = fopen(fname, "w");
    assert(fp);
    for (i = 0; i < size; i++) {
        fprintf(fp, "%g %g\n", ary[i].influence, ary[i].weight);
    }
    res = fclose(fp);
    assert(res == 0);
}
