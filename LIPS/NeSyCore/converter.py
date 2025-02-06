import ast

class Converter(ast.NodeVisitor):
    """
    Convert infix expression to prefix expression
    used for scaler
    """
    def __init__(self):
        self.prefix_expr = ""
        
    def prefix2infix(self, expression):
        self.prefix_expr = expression.replace("(", " ( ").replace(")", " ) ").split()
        self.prefix_expr.reverse()
        return self.parse_expression()
    
    def parse_expression(self):
        token = self.prefix_expr.pop()

        if token == '(':
            operator = self.prefix_expr.pop()

            # UnaryOp or binary Op
            expr1 = self.parse_expression()
            if self.prefix_expr[-1] == ")":
                self.prefix_expr.pop()
                if operator in {"-", "sqrt", "abs"}:                    
                    return f"{operator}({expr1})"
                else:
                    raise ValueError(f"Unsupported unary operator: {operator}")
            else:
                # binary Op
                expr2 = self.parse_expression()
                self.prefix_expr.pop()
                return f"({expr1} {operator} {expr2})"

        return token

    def infix2prefix(self, expression):
        self.prefix_expr = ""
        tree = ast.parse(expression, mode='eval')
        self.visit(tree.body)
        return self.prefix_expr.strip()

    def visit_BinOp(self, node):
        op = self.get_operator(node.op)
        self.prefix_expr += f"({op} "
        self.visit(node.left)
        self.prefix_expr += " "
        self.visit(node.right)
        self.prefix_expr += ")"

    def visit_Constant(self, node):
        self.prefix_expr += str(node.value)

    def get_operator(self, op):
        # get operator
        if isinstance(op, ast.Add):
            return "+"
        elif isinstance(op, ast.Sub):
            return "-"
        elif isinstance(op, ast.Mult):
            return "*"
        elif isinstance(op, ast.Div):
            return "/"
        elif isinstance(op, ast.Pow): 
            return "^"
        elif isinstance(op, ast.Mod):
            return "mod"
        else:
            raise ValueError(f"Unsupported operator: {op}")

    def visit_UnaryOp(self, node):
        # handle unary operator
        op = self.get_unary_operator(node.op)
        self.prefix_expr += f"({op} "
        self.visit(node.operand)
        self.prefix_expr += ")"

    def get_unary_operator(self, op):
        if isinstance(op, ast.USub):
            return "-"
        else:
            raise ValueError(f"Unsupported unary operator: {op}")

    def visit_Name(self, node):
        # handle variable
        self.prefix_expr += str(node.id)

    def visit_Call(self, node):
        # handle function call
        func_name = node.func.id
        self.prefix_expr += f"({func_name} "
        for i, arg in enumerate(node.args):
            if i > 0:
                self.prefix_expr += " "
            self.visit(arg)
        self.prefix_expr += ")"