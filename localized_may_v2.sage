import math

class MayE1:

    def __init__(self, localizaton_amount : int, ts_min : int, ts_max : int, distance_to_line : int) -> None:
        self.localization_amount = localizaton_amount
        self.ts_min = ts_min
        self.ts_max = ts_max
        self.distance_to_line = distance_to_line

        self.variables = []
        for i in range(1, int(math.log2(ts_max + 2)) + 1):
            for j in range(0, int(math.log2(ts_max + 1)) + 1):
                degree = ((2**i) - 1) * (2**j) - 1
                if degree <= ts_max:
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

        # Ensure correct and consistent sorting of all lists
        self.variables.sort(key = lambda x : self.variable_ts_degrees[self.ring(x[0])])
        self.gens = sorted(self.ring.gens(), key = lambda x : self.variable_ts_degrees[x])
        self.localized_variables = self.gens[:localizaton_amount]
        if localizaton_amount == 0:
            self.nonnegative_variables = self.gens
        else:
            self.nonnegative_variables = self.gens[localizaton_amount - 1:]
        self.positive_variables = self.nonnegative_variables[1:]

        # Upper boundary line parameters
        self.base_negative_ts = sum([self.variable_ts_degrees[variable] for variable in self.localized_variables])
        self.slope = 1 / self.variable_ts_degrees[self.positive_variables[0]]
        self.constant_term = - self.localization_amount - self.slope * self.base_negative_ts 

        self.unprojected_d1_values = {}
        self.weighted_integer_vectors = {}
        self.minneg_monomials = {}
        self.monomials = {}
        
    
    def ts_degree(self, polynomial) -> int:
        # Returns the (t - s)-degree of a (t - s)-homogeneous polynomial.
        degree = 0
        monomial = polynomial.monomials[0]
        for variable in monomial.variables():
            degree += monomial.degree(variable) * self.variable_ts_degrees[variable]
        return degree


    def s_degree(self, polynomial) -> int:
        # Returns the s-degree of an s-homogeneous polynomial.
        degree = 0
        monomial = polynomial.monomials[0]
        for variable in polynomial.monomials:
            degree += monomial.degree(variable) * self.variable_s_degrees[variable]
        return degree 


    def monomial_tuple(self, monomial):
        return tuple([monomial.degree(variable) for variable in monomial.variables()])


    def tuple_monomial(self, tup):
        return self.ring({tup : 1})


    def remove_variable(self, monomial, variable_to_remove):
        return self.tuple_monomial(tuple([monomial.degree(variable) if variable != variable_to_remove else 0 for variable in monomial.variables()]))
    

    def line_height(self, ts_degree):
        return self.slope * ts_degree + self.constant_term


    def above_line(self, degree_pair):
        ts, s = degree_pair
        return s - self.line_height(ts) > 0.000001


    def project(self, polynomial):
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
    
    
    def unprojected_variable_d1(self, variable):
        try:
            result = self.unprojected_d1_values[variable]
        except KeyError:
            result = self.ring("0")
            i, j = self.variable_ij[variable]
            for k in range(1, i):
                factor1 = self.ij_variable[(i - k, j + k)]
                factor2 = self.ij_variable[(k, j)]
                result += factor1 * factor2
            if variable in self.localized_variables:
                result = variable**2 * result 
            self.unprojected_d1_values[variable] = result
        return result


    def unprojected_d1(self, polynomial):
        try:
            result = self.d1_values[polynomial]
        except KeyError:
            result = self.compute_d1(polynomial)
            self.d1_values[polynomial] = result
        return result


    def d1(self, polynomial):
        return self.project(self.unprojected_d1(polynomial))


    def compute_d1(self, polynomial):
        if len(polynomial.monomials()) > 1:
            result = self.ring("0")
            for monomial in polynomial.monomials():
                result += self.unprojected_d1(monomial)
        else:
            monomial = polynomial.monomials()[0]
            if monomial.variables() == []:
                return 0
            else:
                variable = monomial.variables()[0]
            result = self.unprojected_d1(variable) * (variable**(monomial.degree(variable) - 1) * self.remove_variable(monomial, variable)) + variable * (self.unprojected_d1(variable**(monomial.degree(variable) - 1) * self.remove_variable(monomial, variable)))
    
    
    def minneg_monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        # Returns a list of all monomials with minimal negative (localized) part in the given bidegree
        try:
            monomials = self.minneg_monomials[degree_pair]
        except KeyError:
            monomials = self.compute_minneg_monomials_in_degree((degree_pair))
            self.minneg_monomials[degree_pair] = monomials
        return monomials


    def compute_minneg_monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        ts, s = degree_pair

        try:
            ts_weighted_integer_vectors = self.weighted_integer_vectors[ts - self.base_negative_ts]
        except KeyError:
            ts_weighted_integer_vectors = WeightedIntegerVectors(ts - self.base_negative_ts, [self.variable_ts_degrees[variable] for variable in self.positive_variables]) # h_1_0 messes up this calculation since it has ts-degree 0, negative sign due to double negative
            self.weighted_integer_vectors[ts] = ts_weighted_integer_vectors
        
        if self.localization_amount == 0:
            ts_s_weighted_integer_vectors = [[0] + list(vector) for vector in ts_weighted_integer_vectors if sum(vector) == s + self.localization_amount]
        else:
            ts_s_weighted_integer_vectors = [[1]*self.localization_amount + list(vector) for vector in ts_weighted_integer_vectors if sum(vector) == s + self.localization_amount]
        
        monomials = [self.tuple_monomial(tuple(vector)) for vector in ts_s_weighted_integer_vectors]
        return sorted(monomials)


    def monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        # Returns a list of all monomials in the given bidegree
        try:
            monomials = self.monomials[degree_pair]
        except KeyError:
            monomials = self.compute_monomials_in_degree(degree_pair)
            self.monomials[degree_pair] = monomials
        return monomials


    def compute_monomials_in_degree(self, degree_pair : tuple[int, int]) -> list:
        ts, s = degree_pair
        monomials = self.minneg_monomials_in_degree(degree_pair)
        if self.localization_amount == 0:
            variables_to_multiply = [self.nonnegative_variables[0]]
        else:
            variables_to_multiply = self.localized_variables
        
        for variable in variables_to_multiply:
            if self.above_line(degree_pair):
                continue
            else:
                monomials += [variable * monomial for monomial in self.monomials_in_degree((ts - self.variable_ts_degrees[variable], s - self.variable_s_degrees[variable]))]

        return monomials
May = MayE1(3, 0, 150, 5)
print(f"Minneg monomials in degree (10, 0): {May.minneg_monomials_in_degree((10, 0))}")
print(f"Monomials in degree (10, 0): {May.monomials_in_degree((10, 0))}")
  
        


