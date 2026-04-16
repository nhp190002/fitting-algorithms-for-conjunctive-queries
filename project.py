from typing import Optional
from itertools import product

class DatabaseSchema:

    def __init__(self, name: str):
        self.name = name
        self.relations = set()
        
    def add_relation(self, R: str, n: int):
        """
        Adds a new relation (table) to the schema,
        where R is the relation symbol (table name)
        and n is the arity (number of columns) of the relation symbol
        """
        self.relations.add((R, n))
        
    def relation_exists(self, R: str, n: int) -> bool:
        """
        Returns
        true if the schema has a relation R of arity n
        and false otherwise
        """
        return (R, n) in self.relations
        
    def get_arity(self, R: str) -> int:
        """
        Returns the arity (number of columns) in the relation R
        """
        for (R2, n) in self.relations:
            if R == R2:
                return n
        return 0
    
    def __str__(self) -> str:
        string = self.name
        string += " = {\n"
        i = 1
        for (R, n) in self.relations:
            string += "  ('"
            string += R
            string += "', "
            string += str(n)
            string += ")"
            if i < len(self.relations):
                string += ","
            string += "\n"
            i += 1
        string += "}"
        return string


class DatabaseInstance:
    
    def __init__(self, name: str, schema: DatabaseSchema):
        self.name = name
        self.schema = schema
        self.facts = set()
        
    def add_fact(self, R: str, A: tuple):
        """
        Adds a new fact to the database,
        where R is the relation symbol (table name),
        A is an n-tuple, and (R, n) is a relation
        """
        if not self.schema.relation_exists(R, len(A)):
            raise ValueError(f"Relation ({R}, {len(A)}) does not exist")
        self.facts.add((R, A))
        
    def get_schema(self) -> DatabaseSchema:
        """
        Returns the schema for the database
        """
        return self.schema
        
    def get_active_domain(self) -> set:
        """
        Returns the active domain of the database,
        i.e., the set of all constant values
        """
        active_domain = set()
        for (R, A) in self.facts:
            for v in A:
                active_domain.add(v)
        return active_domain
    
    def __str__(self) -> str:
        string = self.name
        string += " = {\n"
        i = 1
        for (R, A) in self.facts:
            string += "  ('"
            string += R
            string += "', "
            string += str(A)
            string += ")"
            if i < len(self.facts):
                string += ","
            string += "\n"
            i += 1
        string += "}"
        return string


class LabeledExamples:
    
    def __init__(self, k: int):
        self.arity = k
        self.positive_examples = set()
        self.negative_examples = set()
    
    def add_positive_example(self, I: DatabaseInstance, a: tuple):
        """
        Adds a new positive example for some database,
        where a is a k-tuple
        
        The new example must not already be a negative example
        in order to maintain disjointness
        """
        if len(a) != self.arity:
            raise ValueError()
        pair = (I, a)
        if pair in self.negative_examples:
            raise ValueError()
        self.positive_examples.add(pair)
        
    def add_negative_example(self, I: DatabaseInstance, a: tuple):
        """
        Adds a new negative example for some database,
        where a is a k-tuple
        
        The new example must not already be a positive example
        in order to maintain disjointness
        """
        if len(a) != self.arity:
            raise ValueError()
        pair = (I, a)
        if pair in self.positive_examples:
            raise ValueError()
        self.negative_examples.add(pair)
        
    def get_arity(self) -> int:
        """
        Returns the arity of the examples
        """
        return self.arity
    
    def __str__(self) -> str:
        string = "E+ = {"
        
        i = 1
        for (I, a) in self.positive_examples:
            string += "("
            string += I.name
            string += ", "
            string += str(a)
            string += ")"
            if i < len(self.positive_examples):
                string += ", "
            i += 1
        
        string += "},\nE- = {"
        
        i = 1
        for (I, a) in self.negative_examples:
            string += "("
            string += I.name
            string += ", "
            string += str(a)
            string += ")"
            if i < len(self.negative_examples):
                string += ", "
            i += 1
        
        string += "}"
        return string


class FittingCQ:
    
    def __init__(self, schema: DatabaseSchema, k: int):
        self.schema = schema
        self.arity = k
        a = list()
        for i in range(1, k+1):
            a.append("x" + str(i))
        self.answer_variables = tuple(a)
        self.relational_atoms = set()
    
    def add_relational_atom(self, R: str, B: tuple):
        """
        Adds a relational atom to the clause,
        where R is the relation symbol (table name),
        B is an n-tuple, and (R, n) is a relation
        """
        if len(B) != self.schema.get_arity(R):
            raise ValueError()
        if not all(isinstance(b, str) for b in B):
            raise ValueError()
        pair = (R, B)
        self.relational_atoms.add(pair)
    
    def __str__(self) -> str:
        string = "q"
        string += str(self.answer_variables)
        string += " :- "
        i = 1
        for (R, B) in self.relational_atoms:
            string += R
            string += str(B)
            if i < len(self.relational_atoms):
                string += ", "
            i += 1
        string += "."
        return string


def algorithm_P(I: DatabaseInstance, E: LabeledExamples) -> FittingCQ:
    
    k = E.get_arity()
    schema = I.get_schema()

    def strongest_example():
        I_star = DatabaseInstance("strongest", schema)
        c = "c"
        for R, arity in schema.relations:
            I_star.add_fact(R, tuple([c] * arity))
        return (I_star, tuple([c] * k))

    def direct_product(ex1, ex2):
        I1, a1 = ex1
        I2, a2 = ex2
        I_prod = DatabaseInstance("product", schema)
        facts1_by_rel = {}

        for R, tup in I1.facts:
            facts1_by_rel.setdefault(R, []).append(tup)

        for R, tup_list1 in facts1_by_rel.items():
            for tup1 in tup_list1:
                for R2, tup2 in I2.facts:
                    if R2 == R:
                        new_tup = tuple((tup1[i], tup2[i]) for i in range(len(tup1)))
                        I_prod.add_fact(R, new_tup)

        new_answer = tuple((a1[i], a2[i]) for i in range(k))

        return (I_prod, new_answer)

    def canonical_cq(ex):
        I_final, answer_final = ex
        query = FittingCQ(schema, k)
        all_values = set()

        for R, tup in I_final.facts:
            for v in tup:
                all_values.add(v)

        for v in answer_final:
            all_values.add(v)

        value_to_var = {}
        var_idx = 1

        for val in answer_final:
            if val not in value_to_var:
                value_to_var[val] = f"x{var_idx}"
                var_idx += 1

        for val in sorted(all_values, key=str):
            if val not in value_to_var:
                value_to_var[val] = f"x{var_idx}"
                var_idx += 1

        for R, tup in sorted(I_final.facts):
            var_tup = tuple(value_to_var[val] for val in tup)
            query.add_relational_atom(R, var_tup)

        return query

    e_star = strongest_example()
    
    for pos_example in E.positive_examples:
        e_star = direct_product(e_star, pos_example)

    return canonical_cq(e_star)
    

def algorithm_M(I: DatabaseInstance, E: LabeledExamples) -> FittingCQ:
    
    k = E.get_arity()
    schema = I.get_schema()

    def strongest_example():
        I_star = DatabaseInstance("strongest", schema)
        c = "c"
        for R, arity in schema.relations:
            I_star.add_fact(R, tuple([c] * arity))
        return (I_star, tuple([c] * k))

    def direct_product(ex1, ex2):
        I1, a1 = ex1
        I2, a2 = ex2
        I_prod = DatabaseInstance("product", schema)
        facts1_by_rel = {}

        for R, tup in I1.facts:
            facts1_by_rel.setdefault(R, []).append(tup)

        for R, tup_list1 in facts1_by_rel.items():
            for tup1 in tup_list1:
                for R2, tup2 in I2.facts:
                    if R2 == R:
                        new_tup = tuple((tup1[i], tup2[i]) for i in range(len(tup1)))
                        I_prod.add_fact(R, new_tup)

        new_answer = tuple((a1[i], a2[i]) for i in range(k))
        return (I_prod, new_answer)

    def canonical_cq(ex):
        I_final, answer_final = ex
        query = FittingCQ(schema, k)
        all_values = set()

        for R, tup in I_final.facts:
            for v in tup:
                all_values.add(v)

        for v in answer_final:
            all_values.add(v)

        value_to_var = {}
        var_idx = 1

        for val in answer_final:
            if val not in value_to_var:
                value_to_var[val] = f"x{var_idx}"
                var_idx += 1

        for val in sorted(all_values, key=str):
            if val not in value_to_var:
                value_to_var[val] = f"x{var_idx}"
                var_idx += 1

        for R, tup in sorted(I_final.facts):
            var_tup = tuple(value_to_var[val] for val in tup)
            query.add_relational_atom(R, var_tup)

        return query

    def query_holds_on_example(ex_query, I_target: DatabaseInstance, a_target: tuple) -> bool:
        """
        ex_query is an example (I_q, a_q) representing the canonical CQ of I_q
        with answer tuple a_q.

        This checks whether that CQ returns a_target on I_target.
        """
        I_q, a_q = ex_query

        values = set()
        for R, tup in I_q.facts:
            for v in tup:
                values.add(v)
        for v in a_q:
            values.add(v)

        values = list(values)
        target_domain = list(I_target.get_active_domain())

        if len(target_domain) == 0:
            return len(values) == 0 and len(a_target) == 0

        forced_map = {}
        for i in range(k):
            forced_map[a_q[i]] = a_target[i]

        free_values = [v for v in values if v not in forced_map]

        for assignment_tuple in product(target_domain, repeat=len(free_values)):
            h = dict(forced_map)

            for idx, v in enumerate(free_values):
                h[v] = assignment_tuple[idx]

            valid = True
            for R, tup in I_q.facts:
                mapped_tup = tuple(h[v] for v in tup)
                if (R, mapped_tup) not in I_target.facts:
                    valid = False
                    break

            if valid:
                return True

        return False

    def fits_labeled_examples(ex_query) -> bool:
        for (I_pos, a_pos) in E.positive_examples:
            if not query_holds_on_example(ex_query, I_pos, a_pos):
                return False

        for (I_neg, a_neg) in E.negative_examples:
            if query_holds_on_example(ex_query, I_neg, a_neg):
                return False

        return True

    def minimize(ex):
        """
        Greedily remove facts as long as the resulting canonical CQ
        still fits all labeled examples.
        """
        I_curr, a_curr = ex
        changed = True

        while changed:
            changed = False
            current_facts = list(I_curr.facts)

            for fact_to_remove in current_facts:
                I_candidate = DatabaseInstance("candidate", schema)

                for fact in I_curr.facts:
                    if fact != fact_to_remove:
                        I_candidate.add_fact(fact[0], fact[1])

                candidate_ex = (I_candidate, a_curr)

                if fits_labeled_examples(candidate_ex):
                    I_curr = I_candidate
                    changed = True
                    break

        return (I_curr, a_curr)

    e_star = strongest_example()

    for pos_example in E.positive_examples:
        e_star = direct_product(e_star, pos_example)
        e_star = minimize(e_star)

    return canonical_cq(e_star)
    

def algorithm_B(I: DatabaseInstance, E: LabeledExamples) -> FittingCQ:
    query = FittingCQ(I.get_schema(), E.get_arity())
    
    # TODO
    
    return query
    
def algorithm_R(I: DatabaseInstance, E: LabeledExamples) -> Optional[FittingCQ]:
    
    # TODO
    
    return None


S = DatabaseSchema("S")
S.add_relation("Businessman", 1)
S.add_relation("Economist", 1)
S.add_relation("Democrat", 1)
S.add_relation("Republican", 1)
S.add_relation("Father", 2)

print(S)
print()

I = DatabaseInstance("I", S)
I.add_fact("Businessman", ("donald", ))
I.add_fact("Businessman", ("fred", ))
I.add_fact("Businessman", ("james", ))
I.add_fact("Economist", ("barack-sr", ))
I.add_fact("Democrat", ("barack", ))
I.add_fact("Democrat", ("franklin", ))
I.add_fact("Republican", ("donald", ))
I.add_fact("Father", ("barack-sr", "barack", ))
I.add_fact("Father", ("fred", "donald", ))
I.add_fact("Father", ("james", "franklin", ))

print(I)
print()
print(f"adom(I) = {I.get_active_domain()}")
print()

E1 = LabeledExamples(1)
E1.add_positive_example(I, ("franklin", ))
E1.add_positive_example(I, ("barack", ))
E1.add_negative_example(I, ("donald", ))

E2 = LabeledExamples(1)
E2.add_positive_example(I, ("franklin", ))
E2.add_positive_example(I, ("donald", ))
E2.add_negative_example(I, ("barack", ))

# print("----------------")
# print()

print("TEST CASE 1")
# print()

# print(E1)
# print()

print(f"{algorithm_P(I, E1)}")
# print(f"{algorithm_M(I, E1)}")
# print(f"{algorithm_B(I, E1)}")
# print(f"{algorithm_R(I, E1)}")
# print()

# q = FittingCQ(S, 1)
# q.add_relational_atom("Democrat", ("x1", ))

# print(q)
# print()

# print("----------------")
# print()

print("TEST CASE 2")
# print()

# print(E2)
# print()

print(f"{algorithm_P(I, E2)}")
# print(f"{algorithm_M(I, E2)}")
# print(f"{algorithm_B(I, E2)}")
# print(f"{algorithm_R(I, E2)}")
# print()

# q = FittingCQ(S, 1)
# q.add_relational_atom("Father", ("x2", "x1"))
# q.add_relational_atom("Businessman", ("x2", ))

# print(q)
# print()
