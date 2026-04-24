#!/usr/bin/env python3
"""
Convert LaTeX volumes to TTS-friendly markdown with all mathematical notation
converted to natural language.
"""

import re
import os
import sys

def convert_math_to_text(text):
    """Convert mathematical notation to natural language descriptions."""
    
    # Common mathematical symbols and their text equivalents
    replacements = [
        # Greek letters
        (r'\\alpha', 'alpha'),
        (r'\\beta', 'beta'),
        (r'\\gamma', 'gamma'),
        (r'\\delta', 'delta'),
        (r'\\epsilon', 'epsilon'),
        (r'\\varepsilon', 'epsilon'),
        (r'\\zeta', 'zeta'),
        (r'\\eta', 'eta'),
        (r'\\theta', 'theta'),
        (r'\\iota', 'iota'),
        (r'\\kappa', 'kappa'),
        (r'\\lambda', 'lambda'),
        (r'\\mu', 'mu'),
        (r'\\nu', 'nu'),
        (r'\\xi', 'xi'),
        (r'\\pi', 'pi'),
        (r'\\rho', 'rho'),
        (r'\\sigma', 'sigma'),
        (r'\\tau', 'tau'),
        (r'\\upsilon', 'upsilon'),
        (r'\\phi', 'phi'),
        (r'\\varphi', 'phi'),
        (r'\\chi', 'chi'),
        (r'\\psi', 'psi'),
        (r'\\omega', 'omega'),
        (r'\\Gamma', 'Gamma'),
        (r'\\Delta', 'Delta'),
        (r'\\Theta', 'Theta'),
        (r'\\Lambda', 'Lambda'),
        (r'\\Xi', 'Xi'),
        (r'\\Pi', 'Pi'),
        (r'\\Sigma', 'Sigma'),
        (r'\\Phi', 'Phi'),
        (r'\\Psi', 'Psi'),
        (r'\\Omega', 'Omega'),
    ]
    
    for pattern, replacement in replacements:
        text = text.replace(pattern, replacement)
    
    # Process inline math $...$ and display math $$...$$
    # This is complex, so we'll do it carefully
    def replace_inline_math(match):
        math_content = match.group(1)
        return convert_math_expression(math_content)
    
    def replace_display_math(match):
        math_content = match.group(1)
        return "\n\n" + convert_math_expression(math_content) + "\n\n"
    
    # Replace display math first ($$...$$)
    text = re.sub(r'\$\$(.*?)\$\$', replace_display_math, text, flags=re.DOTALL)
    
    # Replace inline math ($...$)
    text = re.sub(r'\$([^\$]+)\$', replace_inline_math, text)
    
    return text

def convert_math_expression(expr):
    """Convert a mathematical expression to natural language."""
    expr = expr.strip()
    
    # Handle common patterns
    # Subscripts and superscripts
    expr = re.sub(r'([a-zA-Z])_\{([^\}]+)\}', r'\1 sub \2', expr)
    expr = re.sub(r'([a-zA-Z])_([a-zA-Z0-9])', r'\1 sub \2', expr)
    expr = re.sub(r'([a-zA-Z])\^\{([^\}]+)\}', r'\1 to the power of \2', expr)
    expr = re.sub(r'([a-zA-Z])\^([a-zA-Z0-9])', r'\1 to the power of \2', expr)
    
    # Function application
    expr = re.sub(r'\\mathrm\{([^\}]+)\}', r'\1', expr)
    expr = re.sub(r'\\text\{([^\}]+)\}', r'\1', expr)
    expr = re.sub(r'\\textit\{([^\}]+)\}', r'\1', expr)
    expr = re.sub(r'\\textbf\{([^\}]+)\}', r'\1', expr)
    expr = re.sub(r'\\emph\{([^\}]+)\}', r'\1', expr)
    
    # Special mathematical symbols
    replacements = [
        (r'\\circ', 'composed with'),
        (r'\\compose', 'composed with'),
        (r'\\rs', 'resonance strength'),
        (r'\\emerge', 'emergence'),
        (r'\\void', 'the void'),
        (r'\\leq', 'less than or equal to'),
        (r'\\geq', 'greater than or equal to'),
        (r'\\neq', 'not equal to'),
        (r'\\approx', 'approximately equal to'),
        (r'\\equiv', 'equivalent to'),
        (r'\\sim', 'similar to'),
        (r'\\times', 'times'),
        (r'\\cdot', 'times'),
        (r'\\div', 'divided by'),
        (r'\\frac\{([^\}]+)\}\{([^\}]+)\}', r'the fraction \1 over \2'),
        (r'\\sqrt\{([^\}]+)\}', r'the square root of \1'),
        (r'\\sum', 'the sum of'),
        (r'\\prod', 'the product of'),
        (r'\\int', 'the integral of'),
        (r'\\lim', 'the limit of'),
        (r'\\max', 'the maximum of'),
        (r'\\min', 'the minimum of'),
        (r'\\inf', 'the infimum of'),
        (r'\\sup', 'the supremum of'),
        (r'\\forall', 'for all'),
        (r'\\exists', 'there exists'),
        (r'\\in', 'in'),
        (r'\\notin', 'not in'),
        (r'\\subset', 'subset of'),
        (r'\\subseteq', 'subset or equal to'),
        (r'\\cup', 'union'),
        (r'\\cap', 'intersection'),
        (r'\\emptyset', 'the empty set'),
        (r'\\to', 'maps to'),
        (r'\\rightarrow', 'maps to'),
        (r'\\leftarrow', 'maps from'),
        (r'\\Rightarrow', 'implies'),
        (r'\\Leftarrow', 'is implied by'),
        (r'\\Leftrightarrow', 'if and only if'),
        (r'\\wedge', 'and'),
        (r'\\vee', 'or'),
        (r'\\neg', 'not'),
        (r'\\mathbb\{R\}', 'the real numbers'),
        (r'\\mathbb\{N\}', 'the natural numbers'),
        (r'\\mathbb\{Z\}', 'the integers'),
        (r'\\mathbb\{Q\}', 'the rationals'),
        (r'\\mathbb\{C\}', 'the complex numbers'),
        (r'\\mathcal\{I\}', 'the ideatic space I'),
        (r'\\mathcal\{([A-Z])\}', r'the space \1'),
        (r'\\mathscr\{([A-Z])\}', r'the script \1'),
        (r'\\IS', 'the ideatic space I'),
        (r'\\R', 'the real numbers'),
        (r'\\N', 'the natural numbers'),
    ]
    
    for pattern, replacement in replacements:
        expr = re.sub(pattern, replacement, expr)
    
    # Clean up remaining braces
    expr = expr.replace('{', '').replace('}', '')
    
    # Handle parentheses and brackets
    expr = expr.replace('\\left(', '(').replace('\\right)', ')')
    expr = expr.replace('\\left[', '[').replace('\\right]', ']')
    expr = expr.replace('\\left|', '|').replace('\\right|', '|')
    
    # Clean up whitespace
    expr = re.sub(r'\s+', ' ', expr).strip()
    
    # If the expression looks like a formula, add context
    if any(word in expr.lower() for word in ['composed', 'resonance', 'emergence', 'function', 'equals', 'sum', 'product']):
        return expr
    else:
        # Just return the cleaned expression
        return expr

def process_tex_content(content):
    """Process LaTeX content and convert to TTS-friendly markdown."""
    
    # First convert math
    content = convert_math_to_text(content)
    
    # Remove LaTeX preamble and document structure
    content = re.sub(r'\\documentclass.*?\\begin\{document\}', '', content, flags=re.DOTALL)
    content = re.sub(r'\\end\{document\}', '', content)
    
    # Remove LaTeX packages and commands
    content = re.sub(r'\\usepackage.*?\n', '', content)
    content = re.sub(r'\\newcommand.*?\n', '', content)
    content = re.sub(r'\\renewcommand.*?\n', '', content)
    content = re.sub(r'\\theoremstyle.*?\n', '', content)
    content = re.sub(r'\\newtheorem.*?\n', '', content)
    content = re.sub(r'\\lstdefinelanguage.*?\n', '', content)
    content = re.sub(r'\\lstset\{.*?\}', '', content, flags=re.DOTALL)
    
    # Convert section commands
    content = re.sub(r'\\part\{([^\}]+)\}', r'\n\n# Part: \1\n', content)
    content = re.sub(r'\\chapter\*?\{([^\}]+)\}', r'\n\n## \1\n', content)
    content = re.sub(r'\\section\*?\{([^\}]+)\}', r'\n\n### \1\n', content)
    content = re.sub(r'\\subsection\*?\{([^\}]+)\}', r'\n\n#### \1\n', content)
    content = re.sub(r'\\subsubsection\*?\{([^\}]+)\}', r'\n\n##### \1\n', content)
    
    # Convert title
    content = re.sub(r'\\title\{(.+?)\}', r'\n# \1\n', content, flags=re.DOTALL)
    content = re.sub(r'\\author\{(.+?)\}', r'\n*\1*\n', content, flags=re.DOTALL)
    content = re.sub(r'\\date\{.*?\}', '', content)
    content = re.sub(r'\\maketitle', '', content)
    
    # Convert environments
    content = re.sub(r'\\begin\{abstract\}', '\n**Abstract:**\n', content)
    content = re.sub(r'\\end\{abstract\}', '\n', content)
    
    # Theorem environments
    for env in ['theorem', 'lemma', 'proposition', 'corollary', 'definition', 
                'example', 'remark', 'interpretation', 'axiom_def', 'proof', 'aside', 'game']:
        content = re.sub(rf'\\begin\{{{env}\}}(\[.*?\])?', f'\n**{env.capitalize()}:**\n', content)
        content = re.sub(rf'\\end\{{{env}\}}', '\n', content)
    
    # Lists
    content = re.sub(r'\\begin\{itemize\}', '', content)
    content = re.sub(r'\\end\{itemize\}', '', content)
    content = re.sub(r'\\begin\{enumerate\}', '', content)
    content = re.sub(r'\\end\{enumerate\}', '', content)
    content = re.sub(r'\\item(?:\[[^\]]*\])?\s*', '\n- ', content)
    
    # Text formatting
    content = re.sub(r'\\textbf\{([^\}]+)\}', r'**\1**', content)
    content = re.sub(r'\\textit\{([^\}]+)\}', r'*\1*', content)
    content = re.sub(r'\\emph\{([^\}]+)\}', r'*\1*', content)
    content = re.sub(r'\\texttt\{([^\}]+)\}', r'`\1`', content)
    
    # Quotes and citations
    content = re.sub(r'\\cite\{[^\}]+\}', '', content)
    content = re.sub(r'\\label\{[^\}]+\}', '', content)
    content = re.sub(r'\\ref\{[^\}]+\}', '', content)
    
    # Special characters
    content = content.replace('\\&', '&')
    content = content.replace('\\%', '%')
    content = content.replace('\\_', '_')
    content = content.replace('\\#', '#')
    content = content.replace('\\~{}', '~')
    content = content.replace('---', '—')
    content = content.replace('--', '–')
    content = content.replace("``", '"')
    content = content.replace("''", '"')
    
    # Remove remaining LaTeX commands (simple pattern)
    content = re.sub(r'\\[a-zA-Z]+\*?(?:\[[^\]]*\])?(?:\{[^\}]*\})*', '', content)
    
    # Clean up multiple newlines
    content = re.sub(r'\n{3,}', '\n\n', content)
    
    # Remove input statements (we'll handle these separately)
    content = re.sub(r'\\input\{[^\}]+\}', '', content)
    
    return content.strip()

def read_and_process_file(filepath, base_dir):
    """Read a .tex file and recursively process any \input{} statements."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except:
        print(f"Warning: Could not read {filepath}")
        return ""
    
    # Find all \input{} statements
    input_pattern = r'\\input\{([^\}]+)\}'
    inputs = re.findall(input_pattern, content)
    
    # Replace each \input with the actual content
    for input_file in inputs:
        # Add .tex if not present
        if not input_file.endswith('.tex'):
            input_file += '.tex'
        
        # Construct full path
        input_path = os.path.join(base_dir, input_file)
        
        if os.path.exists(input_path):
            # Recursively process the input file
            input_content = read_and_process_file(input_path, base_dir)
            # Replace the \input statement with the content
            content = content.replace(f'\\input{{{input_file.replace(".tex", "")}}}', input_content)
        else:
            print(f"Warning: Could not find input file {input_path}")
    
    return content

def convert_volume(input_file, output_file, volume_name):
    """Convert a complete volume from .tex to TTS .md format."""
    base_dir = os.path.dirname(os.path.abspath(input_file))
    
    print(f"Converting {volume_name}...")
    print(f"  Input: {input_file}")
    print(f"  Output: {output_file}")
    
    # Read and process the main file and all its inputs
    content = read_and_process_file(input_file, base_dir)
    
    # Process the LaTeX content
    markdown = process_tex_content(content)
    
    # Write output
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(markdown)
    
    print(f"  ✓ Completed {volume_name}")
    print(f"  Output file size: {len(markdown)} characters\n")

def main():
    base_dir = "/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology"
    
    # Convert Volume 2
    convert_volume(
        os.path.join(base_dir, "Meaning_Games.tex"),
        os.path.join(base_dir, "Vol2_Strategic_Interaction_TTS.md"),
        "Volume 2: Strategic Interaction"
    )
    
    # Convert Volume 5
    convert_volume(
        os.path.join(base_dir, "Vol5_Power.tex"),
        os.path.join(base_dir, "Vol5_Power_TTS.md"),
        "Volume 5: Power, Knowledge, and Ethics"
    )
    
    print("All volumes converted successfully!")

if __name__ == "__main__":
    main()
