#!/usr/bin/python3
import curses 
import random
import itertools
import argparse
import sys

from collections import defaultdict

from lark import Lark, UnexpectedInput
from lark.visitors import Visitor, Interpreter

GRAMMAR = r"""
?program : asn | add | sub | mul | div | mod 
         | concat 
         | loop 
         | lwhile

asn : var ":=" (const | var) 
add : var ":=" var "+" (const | var) 
sub : var ":=" var "-" (const | var)
mul : var ":=" var "*" (const | var) 
div : var ":=" var "/" (const | var)  
mod : var ":=" var "%" (const | var)  

concat : program (";" program)+

loop : "LOOP"i var "DO"i program "END"i
lwhile : "WHILE"i var "!=" "0" "DO"i program "END"i 

var : "x"i NUMBER
const : NUMBER 

%import common.NUMBER
%import common.WS 
%ignore WS
COMMENT: "#" /[^\n]/*
%ignore COMMENT
"""

TU_LOGO = """
▜██████▙ ▅▅
   ▅▅ ██ ██
   ██ ██ ██
   ██ ██ ██
   ██ ▜█ █▛
   BERLIN
"""



class Clean(Visitor):
    """
    Cleans up AST by: 
    - casting numeric terminals to integer 
    """
    def var(self, tree):
        tree.value = int(tree.children[0].value)

    def const(self, tree):
        tree.value = int(tree.children[0].value)

class ObserverDefaultDict(defaultdict):
    """
    Adds a field diff to track added items
    """
    diff = set()
    def __setitem__(self, item, value):
        self.diff.add(item) 
        super().__setitem__(item, value)

class UserAbortException(Exception):
    pass 
    
class Simulate(Interpreter):
    """
    """
    register = ObserverDefaultDict(int)
    
    def __init__(self, code, values = None, step = 0, line = 0, render=True):
        # step "simulate until
        # line "simulate until line is reached
        if values:
            self.register.update(values)

        self.step = 0 
        self.code = code.splitlines()
        self._goto_step = step
        self._goto_line = line 
        self.should_render = render

        if self.should_render:
            self.stdscr = curses.initscr()
            curses.start_color()
            curses.use_default_colors() 
            curses.noecho()
            curses.cbreak()
            curses.curs_set(0)

            if curses.can_change_color():
                curses.init_color(53, 619, 43, 98)
            curses.init_pair(1, 53, -1)

        
        
    def __del__(self):
        if self.should_render:
            self.show_results()
        
            curses.echo()
            curses.nocbreak()
            curses.endwin()

    def show_results(self):
        screen = self.stdscr
        max_y, max_x = screen.getmaxyx()
        screen.clear()
        
        
        # BACKGROUND PATTERN
        random.seed(self.register[0])
        if curses.has_colors():
            for y in range(max_y):
                for x in range(1, max_x-2):
                    screen.addstr(y, x,
                                  random.choice((" ","░","▒","▓","█",
                                                 "▖","▗","▘","▙","▚",
                                                 "▛","▜","▝","▞","▟")),
                                  curses.color_pair(1) | curses.A_DIM)
                screen.addstr(y, max_x - 2, "█", curses.color_pair(1))
                screen.addstr(y, 0, "█", curses.color_pair(1))
        x_margin = max_x // 2 - 15
        y_margin = max((max_y - len(self.register) - 6) // 2, 0)

        # RESULT BOX
        screen.addstr(y_margin + 1, x_margin, "┏━━━━━━━━━━┯━━━━━━━━━━━━━━━━━━┓")
        screen.addstr(y_margin + 2, x_margin, "┃ REGISTER │       WERT       ┃")
        screen.addstr(y_margin + 3, x_margin, "┠──────────┼──────────────────┨")
        screen.addstr(y_margin + 4, x_margin, "┣╾ ")
        screen.addstr(f"x0", curses.A_BOLD)
        screen.addstr("      │ ")
        screen.addstr(f"{self.register[0]:>16}"
                      if self.register[0] < 10e16 else
                      f"{self.register[0]:>16e}", curses.A_BOLD)
        screen.addstr(" ┃")
        screen.addstr(y_margin + 5, x_margin, "┠──────────┴──────────────────┨")
        if len(self.register) > 1:
            screen.addstr(y_margin + 6, x_margin, "┃ REST                        ┃")
        
        for y, register in enumerate(sorted(self.register.items())[1:max_y - 9],
                                     start=y_margin +7):
            reg, val = register
            screen.addstr(y, x_margin, f"┣╾ x{reg:<3}    = ")
            screen.addstr(f"{val:>16}" if val < 10e16 else f"{val:>16e}")
            screen.addstr(" ┃")
        screen.addstr(y+1 if (len(self.register) > 1) else y_margin + 6, x_margin, "┗Press any key to exit━━━━━━━━┛")

        screen.get_wch()
        
    def resolve(self, var):
        """
        Returns value of variable, or constant 
        """
        if var.data == "var":
            return self.register[var.value]
        if var.data == "const":
            return var.value
            
    def asn(self, tree):
        """
        Assignment
        """
        target, val = tree.children
        self.register[target.value] = self.resolve(val)
        
    def add(self, tree):
        """
        Addition
        """
        target, val1, val2 = tree.children
        self.register[target.value] = self.resolve(val1) + self.resolve(val2)
        
    def sub(self, tree):
        """
        Subtraction 
        """
        target, val1, val2 = tree.children
        self.register[target.value] = max(self.resolve(val1) - self.resolve(val2), 0)
    def mul(self, tree):
        """
        Multiplication
        """
        target, val1, val2 = tree.children
        self.register[target.value] = self.resolve(val1) * self.resolve(val2)

    def div(self, tree):
        """
        Integer Division 
        """
        target, val1, val2 = tree.children
        self.register[target.value] = self.resolve(val1) // self.resolve(val2) 

    def mod(self, tree):
        """
        Modulo
        """ 
        target, val1, val2 = tree.children
        self.register[target.value] = self.resolve(val1) % self.resolve(val2)

    def loop(self, tree):
        """
        Visits child program n times, with n given by the value in var
        """
        var, program = tree.children
        for _ in range(self.resolve(var)):
            self.visit(program)

    def lwhile(self, tree):
        """
        Visits child program until value in var is zero 
        """
        var, program = tree.children
        while self.resolve(var) != 0:
            self.visit(program)

    def concat(self, tree):
        """
        Visits all child programs in order
        """
        for program in tree.children:
            self.visit(program)

    def visit(self, tree):
        # Shim to tie tree traversal to ncurses render loop
        if tree.data != "concat":
            self.step += 1
            if (self.step >= self._goto_step and
                tree.meta.line > self._goto_line and
                self._goto_line != -1 and
                self.should_render):
                self.render(tree) 
        
                
        super().visit(tree)
        
        
    def render(self, tree):
        screen = self.stdscr       
        max_y, max_x = screen.getmaxyx()
        
        screen.clear()
        
        # HEADER 
        screen.addstr(0,0, "   REGISTERS    ┃ L# ┃ PROGRAM")
        s = f"STEP {self.step}: {tree.data.upper():>6} "
        screen.addstr(0, max_x - len(s), s) 
        screen.addstr(1,0, "━━━━━━━━━━━━━━━━╋━━━━╇" + "━"*(max_x - 22))
        
        # REGISTER VALUES
        y = itertools.count() 
        for reg, val in sorted(self.register.items()):
            screen.addstr(2 + next(y), 0,
                          f"[x{reg}]".ljust(6) +
                          (f" = {val:^7}" if val < 10e7 else f" = {val:^7.0e}"),
                          curses.A_BOLD if
                          reg in self.register.diff
                          else curses.A_NORMAL)
            screen.addstr("┃")
        self.register.diff.clear()
            
        screen.addstr(len(self.register) + 2, 0, "────────────────┚")

        # DECORATION 
        lines = TU_LOGO.splitlines()
        for y, line in enumerate(lines[:-1], start= max_y - len(lines) - 2):
            screen.addstr(y, max_x - max(len(_) for _ in lines) - 5, line, curses.A_DIM | curses.color_pair(1))
            screen.addstr(y+1,max_x - max(len(_) for _ in lines) -5, lines[-1], curses.A_DIM)

        # CODE 
        t = tree.meta
        ycurr = iter(range(2, max_y))

        page = t.line // (max_y - 2)
        offset = page * (max_y - 2) 
        
        # output unhighlighted lines before highlight 
        for line, y in zip(self.code[offset:t.line-1], ycurr):
            screen.addstr(y, 17, f"{y-2:4}│ {line}")

        # single line highlights
        if t.line == t.end_line:
            y, line = next(ycurr), self.code[t.line-1]
            screen.addstr(y, 17, f"{y-2+offset:4}│ ", curses.A_BOLD)
            screen.addstr(line[:t.column-1])
            screen.addstr(line[t.column-1: t.end_column-1], curses.A_REVERSE | curses.color_pair(1))
            screen.addstr(line[t.end_column-1:])
        # multiline highlights 
        else:
            y, line = next(ycurr), self.code[t.line-1]
            screen.addstr(y, 17, f"{y-2+offset:4}│ ", curses.A_BOLD)
            screen.addstr(line[:t.column-1])
            screen.addstr(line[t.column-1:],
                          curses.A_REVERSE | curses.color_pair(1))

            for line, y in zip(self.code[t.line: t.end_line-1], ycurr):
                screen.addstr(y, 17, f"{y-2+offset:4}│ ", curses.A_BOLD)
                screen.addstr(line, curses.A_BOLD | curses.color_pair(1))

            if t.end_line < (page + 1) * (max_y - 2) -1:
                y, line = next(ycurr), self.code[t.end_line-1]
                screen.addstr(y, 17, f"{y-2+offset:4}│ ", curses.A_BOLD)
                screen.addstr(line[:t.end_column-1],
                              curses.A_REVERSE | curses.color_pair(1))
                screen.addstr(line[t.end_column-1:])
        # unhightlightes lines after highlighted lines 
        for line, y in zip(self.code[t.end_line:], ycurr):
            screen.addstr(y, 17, f"{y-2+offset:4}│ {line}")
        
        for y in ycurr:
            screen.addstr(y, 21, "│")
        screen.addstr(max_y - 1, 21, "┆")

        OPTIONS = ("[N]ext",
                   "[S]tep, skip to",
                   "[L]ine, skip to",
                   "[E]nd, skip to",
                   "[Q]uit")
        for y, option in enumerate(OPTIONS, start = max_y - len(OPTIONS)):
            screen.addstr(y, 0, option, curses.A_DIM)

        screen.addnstr(max_y -1, 22, " LooPy terminal \"LOOP/WHILE Program\" simulator",
                       max_x - 23, curses.A_DIM)
        # PAGE COUNT
        s = f" PAGE[{page+1}/{len(self.code)//(max_y-2) + 1}]"
        screen.addstr(max_y - 1,
                      max_x - len(s) - 1, s)


        # Wait for user input 
        ch = ""
        while ch not in {"n","s","l","e","q"}:
            ch = screen.getkey()

        # Number entry on 's', 'l' 
        if ch in {"s","l"}:
            buff = []
            step_mode = ch == "s"
            screen.addnstr(max_y-1, 22,
                           " SKIP TO " + ("STEP: " if step_mode else "LINE: ") + " "*100,
                           max_x - 23, curses.A_BOLD)
    
            while ch.isnumeric() or ch in {"s","l"}:
                ch = screen.getkey()
                if ch.isnumeric():
                    buff.append(ch)
                screen.addstr(max_y-1, 37, "".join(buff))
            if step_mode:
                self._goto_step = int("".join(buff))
            else:
                self._goto_line = int("".join(buff))
        # Skip to end of execution 
        if ch == "e":
            self._goto_line = -1
        # Quit 
        if ch == "q":
            sys.exit()
     
                
        



        





if __name__ == "__main__":
    parser = Lark(GRAMMAR, start="program", parser="lalr", propagate_positions=True)

  
    # Configure Argparser 
    a_parser = argparse.ArgumentParser(description="Simulate LOOP/WHILE-Programs")
    a_parser.add_argument('program',
                          help="Text file containing program to be simulated") 
    a_parser.add_argument('--no_render', action="store_true", help="don't render UI")
    a_parser.add_argument('--all_vals', action="store_true", help="output all register values")
    
    def is_valid_var(parser, arg):
        try:
            x_n, val = arg.split('=')
            return int(x_n), int(val)
        except ValueError:
            parser.error(f"Invalid variable assignment {arg}.")
            
    a_parser.add_argument('variables', nargs="*",
                          type=lambda x: is_valid_var(a_parser, x),
                          help="Variable values to call program with. "
                               "Format <n>=<val>, e.g. 1=15 2=3 4=12.") 

    args = a_parser.parse_args()

    # Read in code 
    try:
        with open(args.program, "r") as f:
            code = f.read()
    except FileNotFoundError:
        a_parser.error(f"File not found {args.program}")
        sys.exit() 
    
    try: 
        program = parser.parse(code)
    except UnexpectedInput as e:
        sys.exit(f"Input program malformed: {e}") 
        
    program = Clean().visit(program)
    simulator = Simulate(code,
                         values={**{0:0}, **dict(args.variables)},
                         render=not args.no_render)
    try: 
        simulator.visit(program)
        output = simulator.register[0]
        if args.all_vals:
            output = "\n".join(f"{n}\t{v}" for
                               n,v in
                               sorted(simulator.register.items()))
        # since curses is tied to simulator, it needs to be destroyed
        del simulator                    
        print(output)
    except UserAbortException:
        pass
    
        
        
