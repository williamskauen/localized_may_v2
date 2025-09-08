import math
import random
class MayE1:

    def __init__(self, localizaton_amount : int, ts_min : int, ts_max : int, distance_to_line : int, generator_ts_cap : int = 150) -> None:
        self.localization_amount = localizaton_amount
        self.ts_min = ts_min
        self.ts_max = ts_max
        self.distance_to_line = distance_to_line

        self.variables = []
        for i in range(1, int(math.log2(generator_ts_cap + 2)) + 1):
            for j in range(0, int(math.log2(generator_ts_cap + 1)) + 1):
                degree = ((2**i) - 1) * (2**j) - 1
                if degree <= generator_ts_cap:
                    self.variables.append([f"h_{i}_{j}", degree, i, j])
        self.variables.sort(key = lambda x : x[1])
        for i in range(localizaton_amount):
            self.variables[i][0] += "_n"
        self.ring = PolynomialRing(Integers(2), names = [variable[0] for variable in self.variables], order = TermOrder("wdeglex", [variable[1] if variable[1] != 0 else 1 for variable in self.variables]))
        
        self.variable_ts_degrees = {}
        self.variable_s_degrees = {}
        self.variable_ij = {}
        self.ij_variable = {}
        for i, variable in enumerate([self.ring(variable[0]) for variable in self.variables]): # Done this way to ensure correct sorting
            self.variable_ij[variable] = (self.variables[i][2], self.variables[i][3])
            self.ij_variable[self.variable_ij[variable]] = variable
            if i < localizaton_amount:
                self.variable_ts_degrees[variable] = -self.variables[i][1]
                self.variable_s_degrees[variable] = -1
            else:
                self.variable_ts_degrees[variable] = self.variables[i][1]
                self.variable_s_degrees[variable] = 1

        # Ensure consistent sorting of all lists
        self.gens = self.ring.gens()
        self.localized_variables = self.gens[:localizaton_amount]
        if localizaton_amount == 0:
            self.nonnegative_variables = self.gens
        else:
            self.nonnegative_variables = [self.gens[0]] + [variable for variable in self.gens if "n" not in str(variable)]
        self.positive_variables = self.nonnegative_variables[1:]
        self.variables.sort(key = lambda x : (1, x[1]) if variable in self.localized_variables else (self.variable_ts_degrees[self.ring(x[0])], x[1]))

        # Upper boundary line parameters
        self.base_negative_ts = sum([self.variable_ts_degrees[variable] for variable in self.localized_variables])
        self.slope = 1 / self.variable_ts_degrees[self.positive_variables[0]]
        self.constant_term = - self.localization_amount - self.slope * self.base_negative_ts 

        self.base_ring = Integers(2)
        self.grading_group = AdditiveAbelianGroup((0, 0))
        self.noncorrect_variable_d1_values = {}
        self.d1_values = {}
        self.weighted_integer_vectors = {}
        self.minneg_monomials = {}
        self.monomials = {}
        self.d1_matrices = {}
        self.complex = self.make_chain_complex()
        self.smith_differentials = {}
        self.smith_isomorphism = {}
        self.smith_complex, self.smith_isomorphism, self.smith_isomorphism_inverse = self.make_smith_complex()
        self.homology_projections = self.make_homology_projections()
        
    
    def ts_degree(self, polynomial) -> int:
        # Returns the (t - s)-degree of a (t - s)-homogeneous polynomial.
        degree = 0
        if len(polynomial.monomials()) == 0:
            return 0
        monomial = polynomial.monomials()[0]
        for variable in monomial.variables():
            degree += monomial.degree(variable) * self.variable_ts_degrees[variable]
        return degree


    def s_degree(self, polynomial) -> int:
        # Returns the s-degree of an s-homogeneous polynomial.
        degree = 0
        if len(polynomial.monomials()) == 0:
            return 0
        monomial = polynomial.monomials()[0]
        for variable in monomial.variables():
            degree += monomial.degree(variable) * self.variable_s_degrees[variable]
        return degree 


    def monomial_tuple(self, monomial):
        # Takes a monomial and returns a tuple of the exponents.
        if monomial == self.ring("0"):
            return tuple([0 for variable in self.gens])
        else:
            return tuple([monomial.degree(variable) for variable in self.gens])


    def tuple_monomial(self, tup):
        # Takes a tuple of exponents and returns the corresponding monomial.
        return self.ring({tup : 1})


    def remove_variable(self, monomial, variable_to_remove):
        return self.tuple_monomial(tuple([monomial.degree(variable) if variable != variable_to_remove else 0 for variable in self.gens]))
    

    def line_height(self, ts_degree):
        return self.slope * ts_degree + self.constant_term


    def above_line(self, degree_pair):
        ts, s = degree_pair
        if self.localization_amount == 0:
            return s > 2 * self.ts_max - ts + 1
        else:
            return s - self.line_height(ts) > 0.000001


    def polynomial_vector(self, polynomial):
        # Returns a vector representation of a homogeneous polynomial in the monomial basis.
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        return vector(Integers(2), [1 if monomial in polynomial.monomials() else 0 for monomial in self.monomials_in_degree((ts, s))])


    def vector_polynomial(self, vector_representation, degree_pair):
        # Given a vector representation along with a bidegree, returns the polynomial represented by the vector.
        basis = self.monomials_in_degree(degree_pair)
        result = self.ring("0")
        for i, coefficient in enumerate(tuple(vector_representation)):
            result += coefficient * basis[i]
        return result


    def project_E1(self, polynomial):
        # Projects a polynomial in self.ring to the actual E_1 page (this amounts to sending any monomial lacking one of the localized variables to 0).
        result = self.ring("0")
        for monomial in polynomial.monomials():
            survives = True
            for variable in self.localized_variables:
                if variable not in monomial.variables():
                    survives = False
            if survives == True:
                result += monomial
        return result
    
    
    def noncorrect_variable_d1(self, variable):
        # This does NOT return the correct result due to the way the localized variables are implemented. This is corrected in the computation for monomials.
        try:
            result = self.noncorrect_variable_d1_values[variable]
        except KeyError:
            result = self.ring("0")
            i, j = self.variable_ij[variable]
            for k in range(1, i):
                factor1 = self.ij_variable[(i - k, j + k)]
                factor2 = self.ij_variable[(k, j)]
                result += factor1 * factor2
            self.noncorrect_variable_d1_values[variable] = result
        return result


    def d1(self, polynomial):
        try:
            d1_value = self.d1_values[polynomial]
        except KeyError:
            d1_value = self.ring("0")
            for monomial in polynomial.monomials():
                d1_value += self.compute_monomial_d1(monomial)
            self.d1_values[polynomial] = d1_value
        return d1_value


    def compute_monomial_d1(self, monomial):
        # We have to do it in this cursed way due to the way the localized variables are implemented (and in particular because we can't use negative exponents effectively in the polynomial ring, at least as far as i've figured out)
        # The below basically amounts to applying the product rule repeatedly until we only need to calculate d1 of the variables, then doing some math on the exponents to make sure they turn out correct, and dropping terms that won't survive projection to the E1-page
        result = self.ring("0")
        for variable in monomial.variables():
            subresult = self.ring("0")
            exponent = monomial.degree(variable)
            localized = variable in self.localized_variables
            if localized:
                base_factor = -exponent * variable**(exponent + 1) * self.remove_variable(monomial, variable)
            else:
                base_factor = exponent * variable**(exponent - 1) * self.remove_variable(monomial, variable)
            if base_factor == self.ring("0"):
                continue
            base_representation = self.monomial_tuple(base_factor)
            for summand in self.noncorrect_variable_d1(variable).monomials():
                summand_representation = self.monomial_tuple(summand)
                summand_representation = [-variable_exponent if i < self.localization_amount else variable_exponent for i, variable_exponent in enumerate(summand_representation)] # Negative sign due to the localized variables alreadly being persumed to have negative exponent.
                survives = True
                for i in range(self.localization_amount): # Checks if the product of base_factor and summand will project to 0, if so it is discarded:
                    if base_representation[i] + summand_representation[i] <= 0:
                        survives = False
                if not survives:
                    continue
                result_tuple = tuple([base_exponent + summand_exponent for base_exponent, summand_exponent in zip(base_representation, summand_representation)])
                subresult += self.tuple_monomial(result_tuple)
            result += subresult
        return result


    def minneg_monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        # Returns a list of all monomials with minimal negative (localized) part in the given bidegree
        try:
            monomials = self.minneg_monomials[self.grading_group(degree_pair)]
        except KeyError:
            monomials = self.compute_minneg_monomials_in_degree((degree_pair))
            self.minneg_monomials[self.grading_group(degree_pair)] = monomials
        return monomials


    def compute_minneg_monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        ts, s = degree_pair
        new_ts, new_s = ts - self.base_negative_ts, s + self.localization_amount # Negative sing due to double negative

        try:
            ts_weighted_integer_vectors = self.weighted_integer_vectors[new_ts]
        except KeyError:
            ts_weighted_integer_vectors = WeightedIntegerVectors(new_ts, [self.variable_ts_degrees[variable] for variable in self.positive_variables]) # h_1_0 messes up this calculation since it has ts-degree 0
            self.weighted_integer_vectors[new_ts] = ts_weighted_integer_vectors
        
        if self.localization_amount == 0:
            ts_s_weighted_integer_vectors = [[0] + list(vector) for vector in ts_weighted_integer_vectors if sum(vector) == new_s]
        else:
            ts_s_weighted_integer_vectors = [[1]*self.localization_amount + list(vector) for vector in ts_weighted_integer_vectors if sum(vector) == new_s]
        
        monomials = [self.tuple_monomial(tuple(vector)) for vector in ts_s_weighted_integer_vectors]
        return sorted(set(list(monomials))) # Removing duplicates (there shouldn't be any, but do it anyways just to be sure).


    def monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        # Returns a sorted* list of all monomials in the given bidegree (due to the localized variables having weird degrees, the sorting will also be a bit weird, although consistent)
        try:
            monomials = self.monomials[self.grading_group(degree_pair)]
        except KeyError:
            monomials = self.compute_monomials_in_degree(degree_pair)
            self.monomials[self.grading_group(degree_pair)] = monomials
        return monomials


    def compute_monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        # Finds all monomials in a given degree by starting with the minneg ones and then recursively adding those with higher exponents of the localized variables.
        # TODO: Could be made more efficient by eliminating double visitations instead of just discarding duplicates at the end.
        ts, s = degree_pair
        monomials = self.minneg_monomials_in_degree(degree_pair)
        if self.localization_amount == 0:
            for i in range(1, s):
                monomials += [self.nonnegative_variables[0]^(s - i) * monomial for monomial in self.minneg_monomials_in_degree((ts, i))]
            return sorted(list(set(monomials)))
        else:
            variables_to_multiply = self.localized_variables
        
        for variable in variables_to_multiply:
            new_ts, new_s = ts - self.variable_ts_degrees[variable], s - self.variable_s_degrees[variable]
            if self.above_line((new_ts, new_s)) or (self.localization_amount == 0 and s < 0):
                continue
            else:
                monomials += [variable * monomial for monomial in self.monomials_in_degree((new_ts, new_s))]

        return sorted(list(set(monomials))) # Removing duplicates caused by double visitations (for example caused by going h_1_0_n, then h_1_1_n and afterwards h_1_1_n then h_1_0_n).


    def d1_matrix(self, degree_pair : tuple[int, int]):
        # Returns a matrix representing the d1-differential leaving the specified bidegree, with respect to the monomial bases returned by monomials_in_degree
        try:
            d1_matrix = self.d1_matrices[self.grading_group(degree_pair)]
        except KeyError:
            d1_matrix = self.compute_d1_matrix(degree_pair)
            self.d1_matrices[self.grading_group(degree_pair)] = d1_matrix
        return d1_matrix


    def compute_d1_matrix(self, degree_pair : tuple[int, int]):
        ts, s = degree_pair
        domain_basis = self.monomials_in_degree(degree_pair)
        codomain_basis = self.monomials_in_degree((ts - 1, s + 1))
        matrix_columns = []
        for monomial in domain_basis:
            d1_monomials = self.d1(monomial).monomials()
            d1_vector = [1 if basis_monomial in d1_monomials else 0 for basis_monomial in codomain_basis] # This is the matrix column corresponding to monomial
            matrix_columns.append(d1_vector)
        
        d1_matrix = matrix(Integers(2), matrix_columns).transpose()
        return d1_matrix


    def matrix_d1(self, polynomial):
        # For testing purposes
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        return self.vector_polynomial(self.d1_matrix((ts, s)) * self.polynomial_vector(polynomial), (ts - 1, s + 1))


    def make_chain_complex(self):
        # Computes and returns the cohomology of the E1 page, which is the E2 page, in the range specified on creation.
        for ts in range(self.ts_min - 1, self.ts_max + 2):
            line_height = self.line_height(ts)
            if self.localization_amount == 0:
                s_min = 0
                s_max = 2 * self.ts_max - ts + 1
            else: 
                s_min = math.floor(line_height) - self.distance_to_line - 1
                s_max = math.ceil(line_height + 1)
            for s in range(s_min, s_max):
                self.d1_matrix((ts, s))
        # Clean and pad the dictionary to make the ChainComplex constructor happy
        degrees = list(self.d1_matrices.keys())
        for degree in degrees:
            mat = self.d1_matrices[degree]
            if mat.nrows() == 0 and mat.ncols() == 0:
                del(self.d1_matrices[degree])
        degrees = list(self.d1_matrices.keys())
        for degree in degrees:
            mat = self.d1_matrices[degree]
            differential_degree = self.grading_group((-1, 1))
            if degree + differential_degree not in degrees and int(mat.nrows()) != int(0):
                self.d1_matrices[degree + differential_degree] = matrix(self.base_ring, nrows = 0, ncols = mat.nrows())
            if degree - differential_degree not in degrees and int(mat.ncols()) != int(0):
                self.d1_matrices[degree - differential_degree] = matrix(self.base_ring, nrows = mat.ncols(), ncols = 0)
        self.test_matrices()
        return ChainComplex(data = self.d1_matrices, base_ring = self.base_ring, grading_group = self.grading_group, degree_of_differential = self.grading_group((-1, 1)))


    def test_matrices(self):
        for key in self.d1_matrices.keys():
            matrix = self.d1_matrices[key]
            rows, cols = matrix.nrows(), matrix.ncols()
            if key + self.grading_group((-1, 1)) not in self.d1_matrices.keys() and self.d1_matrices[key].nrows() != 0:
                print("error1")
                print(key, rows, cols)
            if key - self.grading_group((-1, 1)) not in self.d1_matrices.keys() and self.d1_matrices[key].ncols() != 0:
                print("error2")
                print(key, rows, cols)


    def make_smith_complex(self):
        differential_degree = self.complex.degree_of_differential()
        degree_tuples = self.complex.ordered_degrees()
        degree_list = []
        smith_differentials = {}
        chain_isomorphism = {}
        chain_isomorphism_inverse = {}
        for degree_tuple in degree_tuples:
            degree_list += list(reversed(degree_tuple))
        for degree in degree_list:
            dimension = self.complex.free_module_rank(degree)
            dimension_below = self.complex.free_module_rank(degree - differential_degree)
            print(degree, dimension, dimension_below)
            d_in = self.complex.differential(degree - differential_degree)
            d_out_rank = self.complex.differential(degree).rank()
            D_1, T_1, S_1_inv = d_in.smith_form()
            T_1_inv, S_1 = T_1.inverse(), S_1_inv.inverse()
            if dimension == 0 and dimension_below == 0:
                continue
            if degree + differential_degree not in degree_list:
                smith_differentials[degree - differential_degree] = D_1
                chain_isomorphism[degree] = T_1_inv.inverse()
                chain_isomorphism[degree - differential_degree] = S_1
                continue

            f = chain_isomorphism[degree]

            new_d_in = f * T_1_inv * D_1
            #assert T_1_inv * D_1 * S_1 == d_in, ("error0", locals())
            #assert f * d_in == new_d_in * S_1, ("error1", locals())
            new_d_in_sub = new_d_in.submatrix(d_out_rank, 0)
            new_d_in_sub, T_2, S_2_inv = new_d_in_sub.smith_form()
            S_2 = S_2_inv.inverse()
            new_d_in = block_matrix([[zero_matrix(self.base_ring, nrows = d_out_rank, ncols = dimension_below)], [new_d_in_sub]])
            Id = identity_matrix(self.base_ring, d_out_rank)
            transform = block_matrix([[Id, 0], [0, T_2]])
            new_f = transform * f
            #new_f = matrix(self.base_ring, [transform * column for column in f.columns()]).transpose() The multiplication above used to cause a SEGFAULT, which i suspect to be due to some weird behavior with 0x0 matrices.
            f_next = S_2 * S_1
            #assert new_f * d_in == new_d_in * f_next, ("error2", locals())
            #f_next = matrix(self.base_ring, [S_2 * column for column in S_1.columns()]).transpose() # Same as above

            smith_differentials[degree - differential_degree] = new_d_in
            chain_isomorphism[degree] = new_f
            chain_isomorphism[degree - differential_degree] = f_next
        
        for degree in degree_list:
            chain_isomorphism_inverse[degree] = chain_isomorphism[degree].inverse()
        print(degree_list)
        return ChainComplex(data = smith_differentials, base_ring = self.base_ring, grading_group = self.grading_group, degree = (-1, 1)), chain_isomorphism, chain_isomorphism_inverse


    def make_homology_projections(self):
        homology_projections = {}
        differential_degree = self.complex.degree_of_differential()
        nonzero_degrees = self.complex.nonzero_degrees()
        for degree in self.smith_isomorphism.keys():
            dimension = self.complex.free_module_rank(degree)
            if degree - differential_degree in nonzero_degrees: 
                d_in_rank = self.complex.differential(degree - differential_degree).rank()
            else:
                d_in_rank = 0
            d_out_rank = self.complex.differential(degree).rank()
            homology_projections[degree] = self.smith_isomorphism_inverse[degree] * block_matrix([[zero_matrix(self.base_ring, nrows = d_in_rank + d_out_rank, ncols = d_in_rank + d_out_rank), 0], [0, identity_matrix(self.base_ring, dimension - d_in_rank - d_out_rank)]]) *  self.smith_isomorphism[degree]
        
        return homology_projections
    
    
    def homology_projection(self, degree_pair):
        degree = self.grading_group(degree_pair)
        differential_degree = self.complex.degree_of_differential()
        try:
            projection = self.homology_projections[degree]
        except KeyError:
            projection = matrix(self.base_ring, nrows = 0, ncols = self.complex.free_module_rank(degree))
        
        return projection


    def project_to_homology(self, polynomial):
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        result = self.vector_polynomial(self.homology_projection((ts, s)) * self.polynomial_vector(polynomial), (ts, s))
        return result

May = MayE1(0, 0, 10, 5, generator_ts_cap = 150)

def run_basic_tests():
    print([f"{variable} : {May.compute_monomial_d1(variable)}" for variable in May.gens])
    print(May.variable_ts_degrees)
    print(f"Minneg monomials in degree (10, 0): {May.minneg_monomials_in_degree((10, 0))}")
    print(f"Monomials in degree (10, 0): {May.monomials_in_degree((10, 0))}")


def run_d1_tests():
    print(f"d1 matrix in degree (10, -1): {May.d1_matrix((10, -1))}")
    works = True
    for monomial_list in list(May.monomials.values()):
        for monomial in monomial_list:
            if May.d1(monomial) != May.matrix_d1(monomial):
                works = False
                print(monomial)
    print(f"d1 matrix works: {works}")

def run_smith_tests():
    works = True
    differential_degree = May.grading_group((-1, 1))
    for degree in May.smith_isomorphism.keys():
        if degree - differential_degree in May.smith_isomorphism.keys():
            if May.smith_isomorphism[degree] * May.complex.differential(degree - differential_degree) != May.smith_complex.differential(degree - differential_degree) * May.smith_isomorphism[degree - differential_degree]:
                works = False
    print(f"Smith complex works : {works}")

def run_other_tests():
    print(May.complex) 

#run_basic_tests()
run_d1_tests()
run_smith_tests()
run_other_tests()


