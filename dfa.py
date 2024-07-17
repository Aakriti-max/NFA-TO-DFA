class Type:
    SYMBOL = 1
    CONCAT = 2
    UNION  = 3
    KLEENE = 4

class ExpressionTree:

    def __init__(self, _type, value=None):
        self._type = _type
        self.value = value
        self.left = None
        self.right = None
    
def constructTree(regexp):
    stack = []
    z = None  # Initialize z variable outside of if-else blocks
    for c in regexp:
        if c.isalpha():
            stack.append(ExpressionTree(Type.SYMBOL, c))
        else:
            if c == "+":
                z = ExpressionTree(Type.UNION)
                z.right = stack.pop()
                z.left = stack.pop()
            elif c == ".":
                z = ExpressionTree(Type.CONCAT)
                z.right = stack.pop()
                z.left = stack.pop()
            elif c == "*":
                z = ExpressionTree(Type.KLEENE)
                z.left = stack.pop()
            stack.append(z)

    return stack[0]

def higherPrecedence(a, b):
    p = ["+", ".", "*"]
    return p.index(a) > p.index(b)

def postfix(regexp):
    temp = []
    for i in range(len(regexp)):
        if i != 0 and (regexp[i-1].isalpha() or regexp[i-1] == ")" or regexp[i-1] == "*")\
            and (regexp[i].isalpha() or regexp[i] == "("):
            temp.append(".")
        temp.append(regexp[i])
    regexp = temp
    
    stack = []
    output = ""

    for c in regexp:
        if c.isalpha():
            output = output + c
            continue

        if c == ")":
            while len(stack) != 0 and stack[-1] != "(":
                output = output + stack.pop()
            stack.pop()
        elif c == "(":
            stack.append(c)
        elif c == "*":
            output = output + c
        elif len(stack) == 0 or stack[-1] == "(" or higherPrecedence(c, stack[-1]):
            stack.append(c)
        else:
            while len(stack) != 0 and stack[-1] != "(" and not higherPrecedence(c, stack[-1]):
                output = output + stack.pop()
            stack.append(c)

    while len(stack) != 0:
        output = output + stack.pop()

    return output

class FiniteAutomataState:
    def __init__(self):
        self.transitions = {}

def evalRegexSymbol(et):
    start_state = FiniteAutomataState()
    end_state   = FiniteAutomataState()
    
    start_state.transitions[et.value] = [end_state]
    return start_state, end_state

def evalRegexConcat(et):
    left_nfa  = evalRegex(et.left)
    right_nfa = evalRegex(et.right)

    left_nfa[1].transitions['epsilon'] = [right_nfa[0]]
    return left_nfa[0], right_nfa[1]

def evalRegexUnion(et):
    start_state = FiniteAutomataState()
    end_state   = FiniteAutomataState()

    up_nfa   = evalRegex(et.left)
    down_nfa = evalRegex(et.right)

    start_state.transitions['epsilon'] = [up_nfa[0], down_nfa[0]]
    up_nfa[1].transitions['epsilon'] = [end_state]
    down_nfa[1].transitions['epsilon'] = [end_state]

    return start_state, end_state

def evalRegexKleene(et):
    start_state = FiniteAutomataState()
    end_state   = FiniteAutomataState()

    sub_nfa = evalRegex(et.left)

    start_state.transitions['epsilon'] = [sub_nfa[0], end_state]
    sub_nfa[1].transitions['epsilon'] = [sub_nfa[0], end_state]

    return start_state, end_state

def evalRegex(et):
    if et._type == Type.SYMBOL:
        return evalRegexSymbol(et)
    elif et._type == Type.CONCAT:
        return evalRegexConcat(et)
    elif et._type == Type.UNION:
        return evalRegexUnion(et)
    elif et._type == Type.KLEENE:
        return evalRegexKleene(et)

def printStateTransitions(state, states_done, symbol_table):
    if state in states_done:
        return

    states_done.append(state)

    for symbol in list(state.transitions):
        line_output = "q" + str(symbol_table[state]) + "\t\t" + ("ε" if symbol == 'epsilon' else symbol) + "\t\t\t"
        for ns in state.transitions[symbol]:
            if ns not in symbol_table:
                symbol_table[ns] = 1 + sorted(symbol_table.values())[-1]
            line_output = line_output + "q" + str(symbol_table[ns]) + " "

        print(line_output)

        for ns in state.transitions[symbol]:
            printStateTransitions(ns, states_done, symbol_table)

def printTransitionTable(finite_automata):
    print("State\t\tSymbol\t\t\tNext state")
    printStateTransitions(finite_automata[0], [], {finite_automata[0]:0})

# DFA Conversion

class DFAState:
    def __init__(self, name):
        self.name = name
        self.transitions = {}

def epsilon_closure(states):
    closure = set(states)
    stack = list(states)
    while stack:
        state = stack.pop()
        if 'epsilon' in state.transitions:
            for next_state in state.transitions['epsilon']:
                if next_state not in closure:
                    closure.add(next_state)
                    stack.append(next_state)
    return closure

def move(states, symbol):
    result = set()
    for state in states:
        if symbol in state.transitions:
            result.update(state.transitions[symbol])
    return result

def dfa_from_nfa(nfa_start_state):
    dfa_start_state = DFAState("q0")
    dfa_states = [dfa_start_state]
    nfa_states = epsilon_closure({nfa_start_state})
    dfa_state_mapping = {tuple(nfa_states): dfa_start_state}

    stack = [(dfa_start_state, nfa_states)]
    while stack:
        dfa_state, nfa_states = stack.pop()
        for symbol in alphabet:
            next_nfa_states = epsilon_closure(move(nfa_states, symbol))
            if next_nfa_states:
                if tuple(next_nfa_states) not in dfa_state_mapping:
                    new_dfa_state = DFAState("q" + str(len(dfa_states)))
                    dfa_states.append(new_dfa_state)
                    dfa_state_mapping[tuple(next_nfa_states)] = new_dfa_state
                    stack.append((new_dfa_state, next_nfa_states))
                dfa_state.transitions[symbol] = dfa_state_mapping[tuple(next_nfa_states)]

    return dfa_start_state, dfa_states

def print_dfa_transition_table(dfa_start_state):
    print("State\t\tSymbol\t\t\tNext state")
    dfa_state_mapping = {dfa_start_state.name: 0}
    print_dfa_state_transitions(dfa_start_state, [], dfa_state_mapping)

def print_dfa_state_transitions(state, states_done, state_mapping):
    if state.name in states_done:
        return

    states_done.append(state.name)

    for symbol in state.transitions:
        next_state = state.transitions[symbol]
        if next_state.name not in state_mapping:
            state_mapping[next_state.name] = len(state_mapping)
        line_output = state.name + "\t\t" + symbol + "\t\t\tq" + str(state_mapping[next_state.name])
        print(line_output)

        print_dfa_state_transitions(next_state, states_done, state_mapping)

# Main Program

alphabet = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

r = input("Enter regex: ")
pr = postfix(r)

nfa = evalRegex(constructTree(pr))
fa_start_state, _ = nfa
dfa_start_state, dfa_states = dfa_from_nfa(fa_start_state)
print("Transition Table for NFA:")
printTransitionTable(nfa)
print("\nTransition Table for DFA:")
print_dfa_transition_table(dfa_start_state)
