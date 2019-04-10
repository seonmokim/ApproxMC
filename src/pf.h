#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "asa241.h"

#define log_choose log_choose_small_k

#define SAMPLES_PER_BIT 10
#define SAMPLES_PER_BITF ((double)SAMPLES_PER_BIT)
#define NUM_SAMPLES 500
#define NUM_SAMPLESF ((double)SAMPLES_PER_BIT*MAX_INFL)

struct Particles {
    double influence;
    double weight;
};

class PF {
public:
    PF()
    {
    }

    ~PF()
    {
    }
   
    double mean_particle(struct Particles ary[], int nSamples);
    double variance_particle(struct Particles ary[], int nSamples);
    double stddev_particle(struct Particles ary[], int nSamples);
    
    double mean_pdf(struct Particles ary[], int nSamples);
    double variance_pdf(struct Particles ary[], int nSamples);
    double stddev_pdf(struct Particles ary[], int nSamples);
    
    void get_uniform_prior(struct Particles ary[NUM_SAMPLES], int nVars, int nSamples);  
    void estimate_posterior_eq_n(int k, int n, struct Particles a[], int nSamples);
    void estimate_posterior_ge_n(int k, int n, struct Particles a[], int nSamples);
    
    void sampling(struct Particles a[], struct Particles b[], int nVars, int nSamples);
    void load_particles(struct Particles a[], struct Particles b[], int nSamples);
    
    double* get_cdf (struct Particles ary[], int nSamples);
    double sum_pdf(struct Particles ary[], int min, int max, int nSamples);
    int get_center_index(struct Particles ary[], int nSamples, double value);
    
    double get_lb(struct Particles ary[], int cen, int nSamples, double confidence);
    double get_ub(struct Particles ary[], int cen, int nSamples, double confidence);
    
    void print_inf(struct Particles ary[], int nSamples);
    void print_weight(struct Particles ary[], int nSamples);


private:
    double log_fact(double n);
    double log_choose_gamma(double n, double k);
    double log_choose_gamma2(double n, double k);
    double log_choose_small_k(double n, int k);
    
    double linear_intep (double a, double b, double w1, double w2);
   
    double prob_eq_n(double bt, int k, int n);
    double prob_ge_n(double bt, int k, int n);
   
    void normalize(struct Particles ary[], int nSamples);
    void set_equal_weight(struct Particles ary[], int nSamples);
    
    void normalize_cdf(double ary[], int nSamples);
    
    double sum_weight(struct Particles ary[], int min, int max);

    void gnuplot_data(const char *fname, struct Particles ary[], int nSamples);
};
