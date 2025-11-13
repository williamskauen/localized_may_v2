import math
import os
import csv
class MayE1:
    
    def __init__(self, localizaton_amount : int, ts_min : int, ts_max : int, distance_to_line : int, generator_ts_cap : int = 150, debug = False) -> None:
        self.localization_amount = localizaton_amount
        self.ts_min = ts_min
        self.ts_max = ts_max
        self.distance_to_line = distance_to_line
        self.debug = debug 
        
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
        self.positive_slope = 1 / self.variable_ts_degrees[self.positive_variables[0]]
        if localizaton_amount > 1:
            self.negative_slope = 1 / max([-self.variable_ts_degrees[variable] for variable in self.localized_variables])
        else:
            self.negative_slope = 1
        self.positive_constant_term = - self.localization_amount - self.positive_slope * self.base_negative_ts
        self.negative_constant_term = - self.localization_amount - self.negative_slope * self.base_negative_ts

        self.base_ring = Integers(2)
        self.grading_group = AdditiveAbelianGroup((0, 0))
        self.noncorrect_variable_d1_values = {}
        self.d1_values = {}
        self.weighted_integer_vectors = {}
        self.minneg_monomials = {}
        self.monomials = {}
        self.d1_matrices = {}
        self.degree_list = []
        self.complex = self.make_chain_complex()
        self.smith_differentials = {}
        self.smith_isomorphism = {}
        self.smith_complex, self.smith_isomorphism, self.smith_isomorphism_inverse = self.make_smith_complex(self.complex)
        self.homology_projections = self.make_homology_projections(self.complex, self.smith_isomorphism, self.smith_isomorphism_inverse)
        self.homology = self.compute_homology()

        if self.localization_amount == 2:
            self.double_localized_E2_lines =  {0 : (("h_1_0_n * h_1_1_n * h_2_0", "0"),),
                        1 : (("h_1_0_n * h_1_1_n^2 * h_2_0", "0"),),
                        2 : (("h_1_0_n^2 * h_1_1_n * h_2_0", "0"), ("h_1_0_n * h_1_1_n^3 * h_2_0", "0")),
                        3 : (("h_1_0_n * h_1_1_n^4 * h_2_0", "0"), ("h_1_0_n * h_1_1_n * h_2_1", "0")),
                        4 : (("h_1_0_n * h_1_1_n^5 * h_2_0", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0", "0"), ("h_1_0_n * h_1_1_n^2 * h_2_0^2 * h_2_1 + h_1_0_n * h_1_1_n * h_2_0 * h_3_0", "0"), ("h_1_0_n * h_1_1_n * h_1_2 * h_2_1", "0")),
                        5 : (("h_1_0_n * h_1_1_n^6 * h_2_0", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0 * h_1_2", "0"), ("h_1_0_n * h_1_1_n^3 * h_2_0^2 * h_2_1 + h_1_0_n * h_1_1_n^2 * h_2_0 * h_3_0", "0"), ("h_1_0_n * h_1_1_n * h_2_0 * h_1_3", "0"), ("h_1_0_n * h_1_1_n * h_1_2^2 * h_2_1", "0")),
                        6 : (("h_1_0_n * h_1_1_n^2 * h_2_0 * h_1_3", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0 * h_1_2^2", "0"), ("h_1_0_n * h_1_1_n^7 * h_2_0", "0"), ("h_1_0_n^2 * h_1_1_n^4 * h_2_0^3 * h_1_2 + h_1_0_n * h_1_1_n^3 * h_2_0 * h_3_0", "0"), ("h_1_0_n^4 * h_1_1_n * h_2_0", "0"), ("h_1_0_n^2*h_1_1_n*h_2_0*h_1_2^4", "0")),
                        7 : (("h_1_0_n * h_1_1_n^2 * h_2_0 * h_2_1^2", "0"), ("h_1_0_n * h_1_1_n^3 * h_2_0 * h_1_3", "0"), ("h_1_0_n * h_1_1_n^8 * h_2_0", "0"), ("h_1_0_n^2 * h_1_1_n * h_2_0 * h_1_3", "0"), ("h_1_0_n^2 * h_1_1_n^5 * h_2_0^3 * h_1_2 + h_1_0_n * h_1_1_n^4 * h_2_0 * h_3_0", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_1", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0 * h_1_2^3", "0"), ("h_1_0_n^2 * h_1_1_n * h_2_0 * h_1_2^5", "0")),
                        8 : (("h_1_0_n * h_1_1_n * h_2_0 * h_3_0^2", "h_1_0_n * h_1_1_n * h_2_0^3 * h_1_3"), ("h_1_0_n * h_1_1_n^3 * h_2_0 * h_2_1^2", "h_1_0_n * h_1_1_n * h_2_0 * h_1_3"), ("h_1_0_n * h_1_1_n^4 * h_2_0 * h_1_3", "0"), ("h_1_0_n * h_1_1_n^9 * h_2_0", "0"), ("h_1_0_n^5 * h_1_1_n * h_2_0", "0"), ("h_1_0_n^3 * h_1_1_n * h_1_2 * h_2_1", "0"), ("h_1_0_n^2 * h_1_1_n^6 * h_2_0^3 * h_1_2 + h_1_0_n * h_1_1_n^5 * h_2_0 * h_3_0", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0 * h_1_2^4", "0"), ("h_1_0_n^2 * h_1_1_n * h_2_0 * h_1_2^6", "0")),
                        9 : (("h_1_0_n * h_1_1_n^10 * h_2_0", "0"), ("h_1_0_n * h_1_1_n^2 * h_2_0 * h_3_0^2", "h_1_0_n * h_1_1_n * h_2_0 * h_2_1^2 + h_1_0_n * h_1_1_n^2 * h_2_0^3 * h_1_3"), ("h_1_0_n * h_1_1_n^5 * h_2_0 * h_1_3", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0 * h_1_3", "0"), ("h_1_0_n * h_1_1_n^4 * h_2_0 * h_2_1^2", "h_1_0_n * h_1_1_n^2 * h_2_0 * h_1_3"), ("h_1_0_n^5 * h_1_1_n * h_2_0 * h_1_2", "0"), ("h_1_0_n^2 * h_1_1_n^7 * h_2_0^3 * h_1_2 + h_1_0_n * h_1_1_n^6 * h_2_0 * h_3_0", "0"), ("h_1_0_n^4 * h_1_1_n * h_2_0 * h_1_2^3", "0"), ("h_1_0_n^3 * h_1_1_n * h_2_0 * h_1_2^5", "0"), ("h_1_0_n * h_1_1_n * h_1_2^6 * h_2_1", "0")),
                        10: (("h_1_0_n * h_1_1_n * h_2_0 * h_1_3^2", "0"), ("h_1_0_n * h_1_1_n^11 * h_2_0", "0"), ("h_1_0_n * h_1_1_n^3 * h_2_0 * h_3_0^2", "h_1_0_n * h_1_1_n^2 * h_2_0 * h_2_1^2 + h_1_0_n * h_1_1_n^3 * h_2_0^3 * h_1_3"), ("h_1_0_n * h_1_1_n^5 * h_2_0 * h_2_1^2", "h_1_0_n * h_1_1_n^3 * h_2_0 * h_1_3"), ("h_1_0_n * h_1_1_n^6 * h_2_0 * h_1_3", "0"), ("h_1_0_n^5 * h_1_1_n * h_2_0 * h_1_2^2", "0"), ("h_1_0_n^2 * h_1_1_n * h_2_0 * h_3_0^2", "h_1_0_n^2 * h_1_1_n * h_2_0^3 * h_1_3"), ("h_1_0_n^2 * h_1_1_n^8 * h_2_0^3 * h_1_2 + h_1_0_n * h_1_1_n^7 * h_2_0 * h_3_0", "0"), ("h_1_0_n^2 * h_1_1_n^2 * h_2_0^3 * h_1_2 * h_2_1^2 + h_1_0_n * h_1_1_n * h_2_0 * h_2_1^2 * h_3_0", "0"), ("h_1_0_n^6 * h_1_1_n * h_2_0", "0"), ("h_1_0_n^4 * h_1_1_n * h_2_0 * h_1_2^4", "0"), ("h_1_0_n^2 * h_1_1_n * h_1_2^5 * h_2_1", "0"), ("h_1_0_n * h_1_1_n * h_1_2^7 * h_2_1", "0"))
                        }

            self.implemented_differentials = {3 : self.d_3}
            self.computed_projections = {2 : self.homology_projections}

            self.E4, self.E4_complex, self.E4_smith_complex, self.E4_smith_isomorphism, self.E4_smith_isomorphism_inverse = self.compute_double_localized_E2n(2, self.homology, self.double_localized_E2_lines)

            self.pages = {2 : self.homology, 4 : self.E4}
        
    
    def ts_degree(self, polynomial) -> int:
        # Returns the (t - s)-degree of a (t - s)-homogeneous polynomial.
        degree = 0
        if len(polynomial.monomials()) == 0:
            raise ValueError("t - s degree of 0 polynomial undefined")
        monomial = polynomial.monomials()[0]
        for variable in monomial.variables():
            degree += monomial.degree(variable) * self.variable_ts_degrees[variable]
        return degree


    def s_degree(self, polynomial) -> int:
        # Returns the s-degree of an s-homogeneous polynomial.
        degree = 0
        if len(polynomial.monomials()) == 0:
            raise ValueError("s degree of 0 polynomial undefined")
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
    

    def positive_line_height(self, ts_degree):
        return self.positive_slope * ts_degree + self.positive_constant_term


    def negative_line_height(self, ts_degree):
        return self.negative_slope * ts_degree + self.negative_constant_term


    def line_height(self, ts_degree):
        if ts_degree >= self.base_negative_ts:
            result = self.positive_line_height(ts_degree)
        else:
            result = self.negative_line_height(ts_degree)
        return result


    def above_line(self, degree_pair):
        ts, s = degree_pair
        if self.localization_amount == 0:
            return s > ts
        else:
            return s - self.line_height(ts) > 0.000001


    def polynomial_vector(self, polynomial, degree_pair, basis = None, page = 1):
        # Returns a vector representation of a homogeneous polynomial in the provided monomial basis.
        monomial_basis = self.monomials_in_degree(degree_pair)
        if page == 1:
            if polynomial == self.ring("0"):
                return vector(self.base_ring, len(monomial_basis) * [0])
            if basis == None:
                result = vector(Integers(2), [1 if monomial in polynomial.monomials() else 0 for monomial in monomial_basis])
            else:
                basis_vectors = []
                for element in basis:
                    element_monomials = element.monomials()
                    basis_vectors.append([1 if monomial in element_monomials else 0 for monomial in monomial_basis])
                result = matrix(self.base_ring, basis_vectors).transpose().solve_right(self.polynomial_vector(polynomial, degree_pair))
        elif page == 2:
            if self.project_to_homology(polynomial) == self.ring("0"):
                return vector(self.base_ring, len(basis) * [0])
            basis_vectors = []
            for element in basis:
                element = self.project_to_homology(element)
                element_monomials = element.monomials()
                basis_vectors.append([1 if monomial in element_monomials else 0 for monomial in monomial_basis])
            try:
                result = matrix(self.base_ring, basis_vectors).transpose().solve_right(self.polynomial_vector(self.project_to_homology(polynomial), degree_pair))
            except ValueError as e:
                print(f"{self.project_to_homology(polynomial)}, {basis_vectors}")
        return result


    def vector_polynomial(self, vector_representation, degree_pair, basis = None, page = 1):
        # Given a vector representation along with a bidegree, returns the polynomial represented by the vector.
        if basis == None:
            basis = self.monomials_in_degree(degree_pair)
        result = self.ring("0")
        for i, coefficient in enumerate(tuple(vector_representation)):
            result += coefficient * basis[i]
        if page != 1:
            result = self.project_to_page(result, page)
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
                summand_representation = [-variable_exponent if i < self.localization_amount else variable_exponent for i, variable_exponent in enumerate(summand_representation)] # Negative sign due to the localized variables alreadly being presumed to have negative exponent.
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
        new_ts, new_s = ts - self.base_negative_ts, s + self.localization_amount # Negative sign due to double negative

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
            if ts == 0:
                monomials = [self.gens[0]^s]
            else:
                for i in range(1, s):
                    monomials += [self.nonnegative_variables[0]^(s - i) * monomial for monomial in self.minneg_monomials_in_degree((ts, i))]
            return sorted(list(set(monomials)))
        else:
            variables_to_multiply = self.localized_variables
        
        for variable in variables_to_multiply:
            new_ts, new_s = ts - self.variable_ts_degrees[variable], s - self.variable_s_degrees[variable]
            if self.above_line((new_ts, new_s)) or (self.localization_amount == 0 and (s < 0 or s > 2 * self.ts_max - ts + 1)):
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
        matrix_columns = []
        for monomial in domain_basis:
            matrix_columns.append(self.polynomial_vector(self.d1(monomial), (ts - 1, s + 1)))
        
        d1_matrix = matrix(Integers(2), matrix_columns).transpose()
        return d1_matrix


    def matrix_d1(self, polynomial):
        # For testing purposes
        if polynomial == self.ring("0"):
            return self.ring("0")
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        return self.vector_polynomial(self.d1_matrix((ts, s)) * self.polynomial_vector(polynomial, (ts, s)), (ts - 1, s + 1))


    def make_chain_complex(self):
        # Computes and returns the cohomology of the E1 page, which is the E2 page, in the range specified on creation.
        for ts in range(self.ts_min - 1, self.ts_max + 2):
            line_height = self.line_height(ts)
            if self.localization_amount == 0:
                s_min = 0
                s_max = self.ts_max + 1
            else: 
                s_min = math.floor(round(line_height - self.distance_to_line - 1 - self.positive_slope, 2))
                s_max = math.ceil(line_height) + 1
            for s in range(s_min, s_max):
                self.d1_matrix((ts, s))
                self.degree_list.append((ts, s))
                if self.debug:
                    print(f"monomials and matrix {(ts, s)}")
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
        #self.test_matrices()
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


    def make_smith_complex(self, chain_complex):
        # Based on code provided to me by my Masters supervisor, Achim Krause. Generalized to work for arbitrary grading groups.
        differential_degree = self.complex.degree_of_differential()
        degree_tuples = chain_complex.ordered_degrees()
        degree_list = []
        smith_differentials = {}
        chain_isomorphism = {}
        chain_isomorphism_inverse = {}
        for degree_tuple in degree_tuples:
            degree_list += list(reversed(degree_tuple))
        for degree in degree_list:
            dimension = chain_complex.free_module_rank(degree)
            dimension_below = chain_complex.free_module_rank(degree - differential_degree)
            if self.debug:
                print(f"smith complex {degree, dimension, dimension_below}")
            d_in = chain_complex.differential(degree - differential_degree)
            d_out_rank = chain_complex.differential(degree).rank()
            D_1, T_1, S_1_inv = d_in.smith_form()
            T_1_inv, S_1 = T_1.inverse(), S_1_inv.inverse()
            if dimension == 0 and dimension_below == 0:
                continue
            if degree + differential_degree not in degree_list:
                smith_differentials[degree - differential_degree] = D_1
                chain_isomorphism[degree] = T_1
                chain_isomorphism[degree - differential_degree] = S_1
                continue

            f = chain_isomorphism[degree]

            new_d_in = f * T_1_inv * D_1
            #assert T_1_inv * D_1 * S_1 == d_in, ("error0", locals())
            #assert f * d_in == new_d_in * S_1, ("error1", locals())
            if new_d_in.nrows() == 0:
                new_d_in_sub = matrix(self.base_ring, nrows = 0, ncols = new_d_in.ncols())
            elif new_d_in.ncols() == 0:
                new_d_in_sub = matrix(self.base_ring, nrows = new_d_in.nrows() - d_out_rank, ncols = 0)
            else:
                new_d_in_sub = new_d_in.submatrix(d_out_rank, 0) # This throws a SEGFAULT if either of the dimensions are 0 (only when working with Z/2-matrices)
            new_d_in_sub, T_2, S_2_inv = new_d_in_sub.smith_form()
            S_2 = S_2_inv.inverse()
            new_d_in = block_matrix([[zero_matrix(self.base_ring, nrows = d_out_rank, ncols = dimension_below)], [new_d_in_sub]])
            Id = identity_matrix(self.base_ring, d_out_rank)
            transform = block_matrix([[Id, 0], [0, T_2]])
            new_f = transform * f
            #new_f = matrix(self.base_ring, [transform * column for column in f.columns()]).transpose() # The multiplication above used to cause a SEGFAULT, which i suspect to be due to some weird behavior with 0x0 matrices.
            f_next = S_2 * S_1
            #assert new_f * d_in == new_d_in * f_next, ("error2", locals())
            #f_next = matrix(self.base_ring, [S_2 * column for column in S_1.columns()]).transpose() # Same as above

            smith_differentials[degree - differential_degree] = new_d_in
            chain_isomorphism[degree] = new_f
            chain_isomorphism[degree - differential_degree] = f_next
        for degree in degree_list:
            chain_isomorphism_inverse[degree] = chain_isomorphism[degree].inverse()
        if self.debug:
            print(degree_list)
        return ChainComplex(data = smith_differentials, base_ring = self.base_ring, grading_group = self.grading_group, degree = (-1, 1)), chain_isomorphism, chain_isomorphism_inverse


    def is_cycle(self, polynomial):
        return self.d1(polynomial) == self.ring("0")


    def make_homology_projections(self, chain_complex, smith_isomorphism, smith_isomorphism_inverse):
        homology_projections = {}
        differential_degree = chain_complex.degree_of_differential()
        nonzero_degrees = chain_complex.nonzero_degrees()
        for degree in smith_isomorphism.keys():
            dimension = chain_complex.free_module_rank(degree)
            if degree - differential_degree in nonzero_degrees: 
                d_in_rank = chain_complex.differential(degree - differential_degree).rank()
            else:
                d_in_rank = 0
            d_out_rank = chain_complex.differential(degree).rank()
            homology_projections[degree] = smith_isomorphism_inverse[degree] * block_matrix([[zero_matrix(self.base_ring, nrows = d_in_rank + d_out_rank, ncols = d_in_rank + d_out_rank), 0], [0, identity_matrix(self.base_ring, dimension - d_in_rank - d_out_rank)]]) *  smith_isomorphism[degree]
        
        return homology_projections
    
    
    def homology_projection(self, degree_pair):
        degree = self.grading_group(degree_pair)
        try:
            projection = self.homology_projections[degree]
            if projection.ncols() == 0 or projection.nrows() == 0:
                projection = matrix(self.base_ring, nrows = 0, ncols = self.complex.free_module_rank(degree))
        except KeyError:
            projection = matrix(self.base_ring, nrows = 0, ncols = self.complex.free_module_rank(degree))
        
        return projection


    def project_to_homology(self, polynomial):
        if polynomial == self.ring("0"):
            return self.ring("0")
        if not self.is_cycle(polynomial):
            raise ValueError(f"{polynomial} is not a cycle.")
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        result = self.vector_polynomial(self.homology_projection((ts, s)) * self.polynomial_vector(polynomial, (ts, s)), (ts, s))
        return result

    
    def compute_homology(self):
        homology_dict = {}
        differential_degree = self.grading_group((-1, 1))
        degrees = [self.grading_group(degree_tuple) for degree_tuple in self.degree_list]
        degrees = [degree for degree in degrees if ((degree + differential_degree in degrees or self.above_line(tuple(degree + differential_degree))) and degree - differential_degree in degrees) or ((tuple(degree)[0] in [0, self.ts_max]) and (not self.above_line(tuple(degree))))]
        for degree in degrees:
            dimension = self.complex.free_module_rank(degree)
            projection_rank = self.homology_projection(degree).rank()
            smith_homology_generators = [vector(self.base_ring, (dimension - i - 1) * [0] + [1] + i * [0]) for i in range(projection_rank)]
            homology_dict[degree] = sorted([self.vector_polynomial(self.smith_isomorphism_inverse[degree] * smith_generator, tuple(degree)) for smith_generator in smith_homology_generators])
        return homology_dict


    def what_hit(self, polynomial):
        if polynomial == self.ring("0"):
            return self.ring("0")
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        degree = self.grading_group((ts, s))
        differential_degree = self.complex.degree_of_differential()
        try:
            solution_vector = self.d1_matrix(tuple(degree - differential_degree)).solve_right(self.polynomial_vector(polynomial, (ts, s)))
        except ValueError:
            print(f"{polynomial} is not hit, or some other error occurred")
            return None
        return self.vector_polynomial(solution_vector, tuple(degree - differential_degree))


    def homology_in_degree(self, degree_pair : tuple) -> list:
        return self.homology[self.grading_group(degree_pair)]

    
    def can_factor_homology(self, polynomial, factor = "h_2_0^2"):
        if self.project_to_homology(olynomial) == self.ring("0"):
            return self.ring("0")
        if factor != None:
            factor = self.ring(factor)
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        factor_ts, factor_s = self.ts_degree(factor), self.s_degree(factor)
        homology_basis = self.homology_in_degree((ts - factor_ts, s - factor_s))
        available_vectors = [self.polynomial_vector(self.project_to_homology(homology_class * factor, (ts, s))) for homology_class in homology_basis]
        try:
            solution_vector = matrix(self.base_ring, available_vectors).transpose().solve_right(self.polynomial_vector(self.project_to_homology(polynomial), (ts, s)))
            solution = self.project_to_homology(self.vector_polynomial(solution_vector, (ts - factor_ts, s - factor_s), homology_basis))
        except ValueError as e:
            print(f"cannot factor out {factor} from {polynomial}, or some other error ocurred")
            raise e
            return None
        return solution


    def write_data_file(self, page_number = 2):
        if page_number == 1:
            homology_classes = []
            for class_list in self.monomials.values():
                homology_classes += class_list
        elif page_number == 2:
            homology_classes = []
            for class_list in self.homology.values():
                homology_classes += class_list
        else:
            if self.localization_amount != 2:
                raise ValueError("This is only implemented for localization amount 2")
            homology_classes = []
            for class_list in self.pages[page_number].values():
                homology_classes += class_list
        if page_number != 1:
            homology_classes = [self.project_to_homology(homology_class) for homology_class in homology_classes]
        homology_classes.sort(key = lambda x : (self.ts_degree(x), self.s_degree(x), str(x)))
        if page_number <= 2:
            distance_to_line = self.distance_to_line
        elif page_number == 4:
            distance_to_line = round(max(self.double_localized_E2_lines.keys()) / 2, 2)
        filename = f"homology_data_l-{self.localization_amount}_p-{page_number}_d-{distance_to_line}_ts-{self.ts_min}-{self.ts_max}.csv"
        os.chdir("homology_data")
        write_data = True
        if filename in os.listdir():
            overwrite = input("Data file with current parameters is alreadly present, do you wish to overwrite? [y/n]: ")
            if overwrite != "y":
                write_data = False
            else:
                os.remove(filename)

        if write_data:
            gens_to_multiply = []
            gen_names = ["h_1_0", "h_1_1"]
            for i in range(0, 2):
                if i < self.localization_amount:
                    gens_to_multiply.append(self.ring(gen_names[i] + "_n"))
                else:
                    gens_to_multiply.append(self.ring(gen_names[i]))
            lines_to_write = []
            lines_to_write.append(["name", f"ts_degree", f"s_degree", f"{str(self.gens[0])}_target", f"{str(self.gens[1])}_target"])
            if self.localization_amount == 0:
                lines_to_write.append(["0"]*6)
            else:
                lines_to_write.append([f"{float(self.positive_slope)}", f"{float(self.negative_slope)}", f"{float(self.positive_constant_term)}", f"{float(self.negative_constant_term)}", f"{float(distance_to_line)}", f"{self.localization_amount}", f"{page_number}"])
            for homology_class in homology_classes:
                class_name = str(homology_class)
                class_ts_degree = self.ts_degree(homology_class)
                class_s_degree = self.s_degree(homology_class)
                if ((class_s_degree < self.line_height(class_ts_degree) - self.distance_to_line) or (class_s_degree > self.line_height(class_ts_degree)) or (class_ts_degree > self.ts_max) or (class_ts_degree < self.ts_min)) and self.localization_amount != 0:
                    continue
                #print((class_s_degree, class_ts_degree))
                targets = []
                for gen in gens_to_multiply:
                    if page_number <= 2:
                        distance_from_line = round(self.line_height(self.ts_degree(gen * homology_class)) - self.s_degree(gen * homology_class), 2)
                    else:
                        distance_from_line = round(self.positive_line_height(self.ts_degree(gen * homology_class)) - self.s_degree(gen * homology_class), 2) # We need positive_line_height here instead, due to the way we are calculating the higher differentials
                    if (distance_from_line < 0 or distance_from_line > distance_to_line) and self.localization_amount != 0:
                        targets.append("")
                        continue
                    if (not self.is_cycle(gen * homology_class) or self.ts_min > self.ts_degree(gen * homology_class) or self.ts_max <= self.ts_degree(gen * homology_class)) and page_number > 1:
                        targets.append("")
                        continue
                    try:
                        if self.project_to_page(gen * homology_class, page_number) in homology_classes: # This is valid since none of the homology representatives change under projection.
                            targets.append(str(self.project_to_page(gen * homology_class, page_number)))
                        else:
                            targets.append("")
                    except TypeError as e:
                        print(homology_class, targets)
                        raise e
                for i, target in enumerate(targets):
                    if target == "0":
                        targets[i] = ""
                lines_to_write.append([class_name, class_ts_degree, class_s_degree, targets[0], targets[1]])


            with open(filename, "w") as f:
                writer = csv.writer(f)
                for line in lines_to_write:
                    writer.writerow(line)

        os.chdir("..")


    def d_3(self, polynomial, E2_lines):
        if self.localization_amount != 2:
            raise ValueError("This is only implemented for localization amount 2")
        polynomial = self.project_to_homology(polynomial)
        result = self.ring("0")
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        line_number = int((self.positive_line_height(ts) - s) * 2) # We have to use positive line height for it to work correctly with the h_2_0-multiplication lines
        line = [[self.project_to_homology(self.ring(x[0])), self.project_to_homology(self.ring(x[1]))] for x in E2_lines[line_number]]
        found = False
        for element, differential in line:
            exponent = int((ts - self.ts_degree(element)) / 2)
            if exponent % 2 == 1 or exponent < 0:
                continue
            if self.project_to_homology(element * self.ring(f"h_2_0^{exponent}")) == polynomial:
                found = True
                result = differential * self.ring(f"h_2_0^{exponent}")
                if exponent % 4 == 2:
                    for monomial in element.monomials():
                        monomial_list = list(self.monomial_tuple(monomial))
                        summand1 = monomial_list.copy()
                        summand2 = monomial_list.copy()
                        
                        # The below corresponds to the May d3-differential of h_2_0^2 being h_1_1^3 + h_1_0 * h_1_2
                        summand1[1] -= 3
                        summand1[2] += exponent - 2
                        if summand1[1] > 0:
                            result += self.tuple_monomial(tuple(summand1))
                        
                        summand2[0] -= 2
                        summand2[2] += exponent - 2
                        summand2[3] += 1 # This is + while the above is - due to the (slightly clunky) way we handle the negative exponents
                        if summand2[0] > 0:
                            result += self.tuple_monomial(tuple(summand2))
                break
            
        if found == False:
            raise ValueError(f"Did not find a match for {polynomial} in line {line_number}.")
        try:
            result = self.project_to_homology(result)
        except ValueError as e:
            print(f"d_3-error \npolynomial = {polynomial} \nresult = {result} \nmonomial_list = {monomial_list} \nsummand1 = {summand1} \nsummand2 = {summand2} \nline_number = {line_number} \nelement = {element} \ndifferential = {differential}")
            raise e
        return result
                    

    def compute_double_localized_E2n(self, n : int, previous_homology : dict, previous_lines : dict):
        differential_degree = self.complex.degree_of_differential()
        differential = self.implemented_differentials[2*n - 1]
        E2n_dict = {}
        max_line_distance = (len(previous_lines.keys()) - 1) / 2
        if self.localization_amount != 2:
            raise ValueError("This is only implemented for localization amount 2")
        if self.distance_to_line < max_line_distance:
            raise ValueError("May class has too small computation range")
        previous_page = {}
        for degree_pair in previous_homology.keys():
            if self.positive_line_height(degree_pair[0]) - degree_pair[1] - max_line_distance < 0.0001: # positive_line_height for same reason as in d_3
                previous_page[degree_pair] = previous_homology[degree_pair]
        
        matrix_dict = {}
        for degree_pair in previous_page.keys():
            matrix_columns = []
            if degree_pair + differential_degree not in previous_page.keys():
                continue
            for homology_class in previous_page[degree_pair]:
                matrix_columns.append(self.polynomial_vector(differential(homology_class, previous_lines), degree_pair + differential_degree, basis = previous_page[degree_pair + differential_degree], page = 2))

            if len(matrix_columns) == 0:
                matrix_dict[degree_pair] = matrix(self.base_ring, nrows = 0, ncols = len(previous_homology[degree_pair]))
            else:
                matrix_dict[degree_pair] = matrix(self.base_ring, matrix_columns).transpose()
            
            if degree_pair - differential_degree not in previous_page.keys():
                matrix_dict[degree_pair - differential_degree] = matrix(self.base_ring, nrows = len(previous_page[degree_pair]), ncols = 0)

        for degree_pair in list(matrix_dict.keys()):
            if degree_pair - differential_degree not in matrix_dict.keys() and matrix_dict[degree_pair].ncols() != 0 and self.debug:
                print(degree_pair, matrix_dict[degree_pair].ncols())
            if matrix_dict[degree_pair].nrows() == 0 and matrix_dict[degree_pair].ncols() == 0:
                del matrix_dict[degree_pair]

        previous_page_complex = ChainComplex(data = matrix_dict, base_ring = self.base_ring, grading_group = self.grading_group, degree_of_differential = differential_degree)
        smith_complex, smith_isomorphism, smith_isomorphism_inverse = self.make_smith_complex(previous_page_complex)
        E2n_projections = self.make_homology_projections(previous_page_complex, smith_isomorphism, smith_isomorphism_inverse)
        self.computed_projections[2*n] = E2n_projections

        degree_pairs = [self.grading_group(degree_pair) for degree_pair in self.degree_list if self.positive_line_height(degree_pair[0]) - degree_pair[1] - max_line_distance < 0.0001]
        E2n_dict = {}
        for degree_pair in degree_pairs:
            if degree_pair in smith_isomorphism.keys():
                dimension = previous_page_complex.free_module_rank(degree_pair)
                projection_rank = E2n_projections[degree_pair].rank()
                smith_homology_generators = [vector(self.base_ring, (dimension - i - 1) * [0] + [1] + i * [0]) for i in range(projection_rank)]
                E2n_dict[degree_pair] = sorted([self.vector_polynomial(smith_isomorphism_inverse[degree_pair] * smith_generator, tuple(degree_pair), basis = previous_page[degree_pair]) for smith_generator in smith_homology_generators])
            else:
                E2n_dict[degree_pair] = []
        return E2n_dict, previous_page_complex, smith_complex, smith_isomorphism, smith_isomorphism_inverse
        

    def project_to_page(self, polynomial, page_number):
        if polynomial == self.ring("0"):
            return self.ring("0")
        ts, s = self.ts_degree(polynomial), self.s_degree(polynomial)
        degree = self.grading_group((ts, s))
        if page_number == 1:
            result = polynomial
        elif page_number == 2:
            result = self.project_to_homology(polynomial)
        else:
            page_number = page_number - (page_number % 2)
            if degree in self.pages[page_number].keys():
                basis = self.pages[page_number - 2][degree]
            else:
                basis = []
            if self.localization_amount != 2:
                raise ValueError("This is only implemented for localization amount 2")
            if degree in self.computed_projections[page_number].keys():
                result = self.vector_polynomial(self.computed_projections[page_number][degree] * self.polynomial_vector(self.project_to_page(polynomial, page_number - 2), (ts, s), basis, page = page_number - 2), (ts, s), basis)
            else:
                result = self.ring("0")
        return result

input_values = input("Do you want to input parameters for the calculation? If not, the defaults in the code will be used [y/n]: ")
if input_values != "y":
    May = MayE1(2, -15, 70, 6, generator_ts_cap = 150, debug = True)
else:
    localization_amount = int(input("Input desired localization amount (number of the h(k)-s to invert): "))
    ts_min = int(input("Input desired t - s start value: "))
    ts_max = int(input("Input desired t - s stop value: "))
    distance_to_line = float(input("Input desired max distance to the vanishing line: "))
    generator_cap = input("Input desired max t - s degree of the generators which should be considered in the computation (leave blank for the default of 150): ")
    debug_mode = input("Type debug if you want to enable debug mode (prints additional information and runs the various tests), leave blank if not: ")
    if generator_cap == "":
        generator_cap = 150
    else:
        generator_cap = int(generator_cap)
    if debug_mode == "debug":
        debug_mode == True
    else:
        debug_mode == False
    May = MayE1(localization_amount, ts_min, ts_max, distance_to_line, generator_cap, debug_mode)

def run_basic_tests():
    print([f"{variable} : {May.compute_monomial_d1(variable)}" for variable in May.gens])
    print(May.variable_ts_degrees)
    print(f"Minneg monomials in degree (10, 0): {May.minneg_monomials_in_degree((10, 0))}")
    print(f"Monomials in degree (10, 0): {May.monomials_in_degree((10, 0))}")


def run_d1_tests():
    works = True
    for degree_pair in May.degree_list:
        print(f"d1-test {degree_pair}")
        for monomial in May.monomials_in_degree(degree_pair):
            if May.d1(monomial) != May.matrix_d1(monomial):
                works = False
                print(f"{monomial} failed matrix d1 test")
    print(f"d1 matrix works: {works}")

def run_smith_tests():
    works = True
    differential_degree = May.grading_group((-1, 1))
    for degree in May.smith_isomorphism.keys():
        print(f"smith-test {degree}")
        if degree - differential_degree in May.smith_isomorphism.keys():
            if May.smith_isomorphism[degree] * May.complex.differential(degree - differential_degree) != May.smith_complex.differential(degree - differential_degree) * May.smith_isomorphism[degree - differential_degree]:
                print(f"{degree} failed smith test")
                works = False
    print(f"Smith complex works : {works}")

def run_homology_projection_test():
    works = True
    homology_classes = []
    for homology_list in May.homology.values():
        homology_classes += homology_list
    for homology_class in homology_classes:
        if May.project_to_homology(homology_class) != homology_class:
            print(f"Homology class {homology_class} changes under projection")
            works = False
    print(f"Homology invariant under projection : {works}")

def run_E2_line_tests():
    for line in May.double_localized_E2_lines.keys():
        for pair in May.double_localized_E2_lines[line]:
            polynomial = May.ring(pair[0])
            line_distance = round(May.positive_line_height(May.ts_degree(polynomial)) - May.s_degree(polynomial), 3)
            if abs(line_distance - round(line/2, 3)) > 0.00001:
                print(line, pair, line_distance)

def run_other_tests():
    print(May.complex) 

if May.debug:
    #run_basic_tests()
    run_d1_tests()
    run_smith_tests()
    run_other_tests()
    run_homology_projection_test()
    if May.localization_amount == 2:
        run_E2_line_tests()

May.write_data_file(page_number = 1)
May.write_data_file()
if May.localization_amount == 2:
    May.write_data_file(page_number = 4)
