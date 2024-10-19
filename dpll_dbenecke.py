#!/usr/bin/env python3
import csv
import random
from collections import defaultdict
import time

def choose_literal(clauses):
    literal_count = defaultdict(int)
    for clause in clauses:
        for literal in clause:
            literal_count[abs(literal)] += 1  # Count occurrences of literals

    # Find the literal with the maximum occurrences
    return max(literal_count, key=literal_count.get)

def main():
    # Initialize empty lists for stack, satisfiable (xS, yS), and unsatisfiable (xU, yU) results
    stack = []
    xS = []
    yS = []
    xU = []
    yU = []
    
    # Specify the file containing the 2SAT problem in CSV format
    filename = "2SAT.cnf.csv"
    
    # Open the CSV file for reading, using UTF-8 encoding
    with open(filename, mode='r', encoding='utf-8-sig') as file:
        clauses = []  # List to store clauses from the file
        count = 0  # Counter to track number of clauses read
        csvFile = csv.reader(file)  # Read the file as a CSV
        
        # Iterate over each line in the CSV file
        for line in csvFile:
            # If the line starts with 'c', it's a comment; we print the problem number
            if line[0] == "c":
                num = line[1]
                print("Problem:", num)
            
            # If the line starts with 'p', it defines the problem's parameters
            # 'num_var' is the number of variables, and 'num_clauses' is the number of clauses
            elif line[0] == "p":
                num_var = int(line[2])
                num_clauses = int(line[3])
            
            # Otherwise, the line contains a clause
            else:
                # Add the clause to the list, converting the first two elements to integers
                clauses.append({int(line[0]), int(line[1])})
                count += 1  # Increment the clause counter
                
                # If we've read the expected number of clauses
                if count == num_clauses:
                    # Start the timer to measure how long the DPLL algorithm takes
                    begin = time.time()
                    
                    # Call the DPLL algorithm on the current set of clauses and stack
                    result = dpll(clauses, stack)
                    
                    # Measure the elapsed time for solving
                    final = time.time() - begin
                    
                    # If the DPLL algorithm returns True, the problem is satisfiable
                    if result:
                        xS.append(num_clauses * 2)  # Record number of literals
                        yS.append(final)  # Record time taken
                        print("Satisfiable")
                    # If False, the problem is unsatisfiable
                    else:
                        xU.append(num_clauses * 2)  # Record number of literals
                        yU.append(final)  # Record time taken
                        print("Unsatisfiable")
                    
                    # Reset the clause counter and clear the clause list for the next problem
                    count = 0
                    clauses = []


def pure_eliminationFind(clauses):
    #1) count when each literal happens by running through the clauses
    literal_count = {}
    for clause in clauses:
        for literal in clause:
            if literal in literal_count: #if the literal is already in the dictionary then add 1 to the count
                literal_count[literal] += 1
            else:
                literal_count[literal] = 1 #if the literal is not already in the dictionary then create the key and set the count to 1

    #2) see which are pure literals
    pure_literals = [] #create a list to keep the pure literals
    for literal in literal_count.keys(): #loop through the dictionary that counted how many times a literal showed
        if -literal not in literal_count:  #check to see if the negation of a literal is in the dictionary (this can be either negation or negation of the negation)
            pure_literals.append(literal)  #if it is not then that means that the literal only appears positively and thus is pure
        
    return pure_literals

def reduction(clauses, variable, value: bool):
    # Initialize an empty list to hold the reduced set of clauses
    reduced = []
    
    # Determine the target literal based on the given variable and value
    target = (1 if value else -1) * variable
    
    # Iterate over each clause in the list of clauses
    for clause in clauses:
        # If the target literal is in the clause, the clause is satisfied
        # so we can replace it with True (indicating it is satisfied)
        if target in clause:
            reduced.append(True)
        
        # If the negation of the target literal is in the clause,
        # we need to remove it because it contradicts the given value
        elif -target in clause:
            # If the clause only contains the negation of the target,
            # it becomes unsatisfiable, so we append False
            if len(clause) == 1:
                reduced.append(False)
            # Otherwise, remove the negated literal from the clause
            # and append the modified clause to the reduced list
            else:
                clause.remove(-target)
                reduced.append(clause)
        
        # If the clause doesn't contain the target or its negation,
        # simply append the clause as is to the reduced list
        else:
            reduced.append(clause)

    # Return the reduced list of clauses
    return reduced

def eliminate(clauses):
    eliminated_clauses = [clause for clause in clauses if not isinstance(clause, bool)]
    return eliminated_clauses


def dpll(clauses, stack):
    assignments = []

    while True:
        valid_clauses = [clause for clause in clauses if isinstance(clause, set)]
        valid_clauses = eliminate(valid_clauses)
        if len(valid_clauses) == 0:
            return True
        if any(len(clause) == 0 for clause in valid_clauses):
            return False  # A contradiction found due to an empty clause


        #pure literal elimination
        pure_literals = []
        pure_literals = pure_eliminationFind(valid_clauses)
        while pure_literals:
            literal = pure_literals.pop(0)
            assignments.append(literal)  # Track assignment
            valid_clauses = reduction(valid_clauses, literal, True)  # Assign literal as True
            valid_clauses = eliminate(valid_clauses)
            # Update pure literals again
            pure_literals = pure_eliminationFind(valid_clauses)
        
        clauses = eliminate(clauses)
        variable = choose_literal(clauses)
        new_clauses = reduction(valid_clauses, variable, True)

        countert = 0
        counterF = 0
        for clause in new_clauses:
            if clause == False:
                countert +=1
        if countert==0:  # Only continue if no contradiction
            stack.append((valid_clauses, assignments.copy()))  # Save state
            new_clauses = eliminate(new_clauses)
            result = dpll(new_clauses,stack)  # Recur with True assignment
            if result is True:
                return True
        else:
            # If True assignment didn't work, backtrack
            valid_clauses, assignments = stack.pop()  # Restore previous state
            # Try assigning False to the variable
            new_clauses = reduction(valid_clauses, variable, False)
            for clause in new_clauses:
                if clause == False:
                    counterF+=1
            if counterF == 0:  # Check if there's no contradiction
                stack.append((valid_clauses, assignments.copy()))  # Save state
                result = dpll(new_clauses,stack)  # Recur
                if result is True:
                    return True
        return False


    
    
if __name__ == "__main__":
    main()