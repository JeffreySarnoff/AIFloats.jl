"""Small source helpers for this specification's labelled equations."""
import re


def statements(source):
    """Yield complete equation/membership statements, including their metadata."""
    pending = []
    for line in source.splitlines():
        if line.lstrip().startswith('---'):
            continue
        if re.match(r'\s*(?:eq|ceq|mb|cmb)\s', line):
            if pending:
                raise ValueError('Unterminated statement: ' + pending[0])
            pending = [line]
        elif pending:
            pending.append(line)
        if pending and re.search(r'\s\.\s*$', line):
            yield '\n'.join(pending)
            pending = []
    if pending:
        raise ValueError('Unterminated statement: ' + pending[0])


def wrap_term(text, indent, width=100):
    """Wrap at whitespace outside string literals, preserving each literal."""
    words = re.findall(r'(?:[^\s"]|"(?:\\.|[^"\\])*")+', text)
    lines = []
    line = indent
    for word in words:
        if line != indent and len(line) + 1 + len(word) > width:
            lines.append(line)
            line = indent
        line += (' ' if line != indent else '') + word
    return '\n'.join(lines + [line])


def format_equation(statement):
    # Only whitespace outside strings is normalized. Labels and metadata survive.
    text = ' '.join(re.findall(r'(?:[^\s"]|"(?:\\.|[^"\\])*")+', statement))
    match = re.fullmatch(r'((?:eq|ceq) \[[^]]+\]) : (.*) (\[metadata ".*"\]) \.', text)
    if not match:
        return statement
    header, body, metadata = match.groups()
    condition = None
    if header.startswith('ceq '):
        body, separator, condition = body.rpartition(' if ')
        if not separator:
            raise ValueError('Conditional equation without a condition: ' + header)
    lhs, separator, rhs = body.partition(' = ')
    if not separator:
        raise ValueError('Equation without a result: ' + header)
    lines = [f'  {header} :', wrap_term(lhs, '    '), wrap_term('= ' + rhs, '    ')]
    if condition is not None:
        lines.append(wrap_term('if ' + condition, '    '))
    lines.append(f'    {metadata} .')
    return '\n'.join(lines)


def format_equations(source):
    for statement in statements(source):
        source = source.replace(statement, format_equation(statement), 1)
    return source
