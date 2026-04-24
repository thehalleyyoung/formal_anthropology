#!/usr/bin/env python3
"""
Full LaTeX to TTS-optimized Markdown Converter
Converts ALL mathematical notation to 100% speakable English
"""

import re
import sys

def convert_math_expr_to_speech(expr):
    """Convert a mathematical expression to natural English speech."""
    expr = expr.strip()
    
    if not expr:
        return ""
    
    # Handle specific patterns first (most specific to least specific)
    
    # Chain notation: a^{[b_1, ..., b_n]}
    expr = re.sub(r'a\^\{\\mathbf\{b\}\}', 'a transmitted through the chain b', expr)
    expr = re.sub(r'a\^\{\\mathbf\{b\}\'\}', 'a transmitted through chain b prime', expr)
    expr = re.sub(r'a\^\{\[([^\]]+)\]\}', r'a transmitted through the sequence \1', expr)
    
    # Subscripts - convert to descriptive names
    expr = re.sub(r'([a-zA-Z])_\{([^}]+)\}', r'\1 sub \2', expr)
    expr = re.sub(r'([a-zA-Z])_([a-zA-Z0-9])', r'\1 sub \2', expr)
    
    # Superscripts
    expr = re.sub(r'([a-zA-Z])\^\{([^}]+)\}', r'\1 to the power \2', expr)
    expr = re.sub(r'([a-zA-Z])\^([a-zA-Z0-9])', r'\1 to the power \2', expr)
    
    # Function calls - MUST be converted to natural language
    # Weight function
    expr = re.sub(r'w\s*\(([^)]+)\)', r'the weight of \1', expr)
    
    # Resonance function - handle both syntaxes
    expr = re.sub(r'\\rs\{([^}]+)\}\{([^}]+)\}', r'the resonance between \1 and \2', expr)
    expr = re.sub(r'\\rs\s*\(([^,]+),\s*([^)]+)\)', r'the resonance between \1 and \2', expr)
    expr = re.sub(r'resonance\s*\(([^,]+),\s*([^)]+)\)', r'the resonance between \1 and \2', expr)
    
    # Emergence function
    expr = re.sub(r'\\emerge\s*\(([^,]+),\s*([^,]+),\s*([^)]+)\)', 
                  r'the emergence when \1 and \2 combine, probed by \3', expr)
    expr = re.sub(r'\\kappa\s*\(([^,]+),\s*([^,]+),\s*([^)]+)\)',
                  r'the emergence when \1 and \2 combine, probed by \3', expr)
    expr = re.sub(r'emergence\s*\(([^,]+),\s*([^,]+),\s*([^)]+)\)',
                  r'the emergence when \1 and \2 combine, probed by \3', expr)
    
    # Chain function
    expr = re.sub(r'\\mathrm\{chain\}\s*\(([^,]+),\s*\[([^\]]*)\]\)',
                  r'the chain starting from \1 through \2', expr)
    expr = re.sub(r'chain\s*\(([^,]+),\s*\[([^\]]*)\]\)',
                  r'the chain starting from \1 through \2', expr)
    
    # Best response
    expr = re.sub(r'BR\s*\(([^,]+),\s*([^)]+)\)', r'the best response of \1 given \2', expr)
    
    # Utility functions
    expr = re.sub(r'u_S\s*\(([^)]+)\)', r'the sender utility for \1', expr)
    expr = re.sub(r'u_R\s*\(([^)]+)\)', r'the receiver utility for \1', expr)
    expr = re.sub(r'u\s*\(([^)]+)\)', r'the utility of \1', expr)
    
    # Supremum, infimum
    expr = re.sub(r'\\sup_\{([^}]+)\}', r'the supremum over \1 of', expr)
    expr = re.sub(r'\\inf_\{([^}]+)\}', r'the infimum over \1 of', expr)
    expr = re.sub(r'\\max_\{([^}]+)\}', r'the maximum over \1 of', expr)
    expr = re.sub(r'\\min_\{([^}]+)\}', r'the minimum over \1 of', expr)
    
    # Sum and product notation
    expr = re.sub(r'\\sum_\{([^}]+)\}\^\{([^}]+)\}', r'the sum from \1 to \2 of', expr)
    expr = re.sub(r'\\sum_\{([^}]+)\}', r'the sum over \1 of', expr)
    expr = re.sub(r'\\prod_\{([^}]+)\}\^\{([^}]+)\}', r'the product from \1 to \2 of', expr)
    expr = re.sub(r'\\prod_\{([^}]+)\}', r'the product over \1 of', expr)
    
    # Absolute value and norms
    expr = re.sub(r'\\left\\?\|([^|]+)\\right\\?\|', r'the absolute value of \1', expr)
    expr = re.sub(r'\|([^|]+)\|', r'the absolute value of \1', expr)
    
    # Fractions
    expr = re.sub(r'\\frac\{([^}]+)\}\{([^}]+)\}', r'\1 divided by \2', expr)
    
    # Square root
    expr = re.sub(r'\\sqrt\{([^}]+)\}', r'the square root of \1', expr)
    
    # Limits
    expr = re.sub(r'\\lim_\{([^}]+)\\to([^}]+)\}', r'the limit as \1 approaches \2 of', expr)
    
    # Integrals
    expr = re.sub(r'\\int_\{([^}]+)\}\^\{([^}]+)\}', r'the integral from \1 to \2 of', expr)
    expr = re.sub(r'\\int', ' the integral of ', expr)
    
    # Expectation
    expr = re.sub(r'\\mathbb\{E\}\[([^\]]+)\]', r'the expected value of \1', expr)
    expr = re.sub(r'\\mathbb\{E\}', ' expectation ', expr)
    
    # Probability
    expr = re.sub(r'\\mathbb\{P\}\[([^\]]+)\]', r'the probability of \1', expr)
    expr = re.sub(r'\\mathbb\{P\}', ' probability ', expr)
    
    # Special sets and spaces
    expr = expr.replace(r'\IS', ' the ideatic space ')
    expr = expr.replace(r'\mathcal{I}', ' the ideatic space ')
    expr = expr.replace(r'\R', ' the real numbers ')
    expr = expr.replace(r'\mathbb{R}', ' the real numbers ')
    expr = expr.replace(r'\N', ' the natural numbers ')
    expr = expr.replace(r'\mathbb{N}', ' the natural numbers ')
    expr = expr.replace(r'\mathbb{Z}', ' the integers ')
    expr = expr.replace(r'\mathbb{Q}', ' the rational numbers ')
    expr = expr.replace(r'\mathbb{C}', ' the complex numbers ')
    
    # Composition operators
    expr = expr.replace(r'\compose', ' composed with ')
    expr = expr.replace(r'\circ', ' composed with ')
    
    # Special symbols
    expr = expr.replace(r'\void', ' the void ')
    expr = expr.replace(r'\varepsilon', ' epsilon ')
    expr = expr.replace(r'\epsilon', ' epsilon ')
    expr = expr.replace(r'\delta', ' delta ')
    expr = expr.replace(r'\Delta', ' Delta ')
    expr = expr.replace(r'\mu', ' mu ')
    expr = expr.replace(r'\sigma', ' sigma ')
    expr = expr.replace(r'\Sigma', ' Sigma ')
    expr = expr.replace(r'\lambda', ' lambda ')
    expr = expr.replace(r'\Lambda', ' Lambda ')
    expr = expr.replace(r'\alpha', ' alpha ')
    expr = expr.replace(r'\beta', ' beta ')
    expr = expr.replace(r'\gamma', ' gamma ')
    expr = expr.replace(r'\Gamma', ' Gamma ')
    expr = expr.replace(r'\theta', ' theta ')
    expr = expr.replace(r'\Theta', ' Theta ')
    expr = expr.replace(r'\phi', ' phi ')
    expr = expr.replace(r'\Phi', ' Phi ')
    expr = expr.replace(r'\psi', ' psi ')
    expr = expr.replace(r'\Psi', ' Psi ')
    expr = expr.replace(r'\omega', ' omega ')
    expr = expr.replace(r'\Omega', ' Omega ')
    expr = expr.replace(r'\kappa', ' emergence ')
    expr = expr.replace(r'\emerge', ' emergence ')
    expr = expr.replace(r'\rs', ' resonance ')
    
    # Comparison operators - convert to words
    expr = expr.replace(r'\leq', ' is at most ')
    expr = expr.replace(r'\geq', ' is at least ')
    expr = expr.replace(r'\le', ' is at most ')
    expr = expr.replace(r'\ge', ' is at least ')
    expr = expr.replace('<=', ' is at most ')
    expr = expr.replace('>=', ' is at least ')
    expr = expr.replace(r'\neq', ' does not equal ')
    expr = expr.replace(r'\ne', ' does not equal ')
    expr = expr.replace(r'\approx', ' is approximately ')
    expr = expr.replace(r'\equiv', ' is equivalent to ')
    expr = expr.replace(r'\sim', ' is similar to ')
    
    # Arrow operators
    expr = expr.replace(r'\to', ' approaches ')
    expr = expr.replace(r'\rightarrow', ' goes to ')
    expr = expr.replace(r'\leftarrow', ' comes from ')
    expr = expr.replace(r'\Rightarrow', ' implies ')
    expr = expr.replace(r'\Leftarrow', ' is implied by ')
    expr = expr.replace(r'\Leftrightarrow', ' if and only if ')
    expr = expr.replace(r'\iff', ' if and only if ')
    expr = expr.replace(r'\implies', ' implies ')
    
    # Arithmetic operators as words
    expr = expr.replace(r'\pm', ' plus or minus ')
    expr = expr.replace(r'\mp', ' minus or plus ')
    expr = expr.replace(r'\times', ' times ')
    expr = expr.replace(r'\cdot', ' times ')
    expr = expr.replace(r'\div', ' divided by ')
    
    # Dots
    expr = expr.replace(r'\cdots', ' and so on ')
    expr = expr.replace(r'\ldots', ' and so on ')
    expr = expr.replace(r'\dots', ' and so on ')
    
    # Set notation
    expr = expr.replace(r'\in', ' in ')
    expr = expr.replace(r'\notin', ' not in ')
    expr = expr.replace(r'\subset', ' is a subset of ')
    expr = expr.replace(r'\subseteq', ' is a subset of or equals ')
    expr = expr.replace(r'\supset', ' is a superset of ')
    expr = expr.replace(r'\supseteq', ' is a superset of or equals ')
    expr = expr.replace(r'\cup', ' union ')
    expr = expr.replace(r'\cap', ' intersection ')
    expr = expr.replace(r'\setminus', ' minus ')
    expr = expr.replace(r'\emptyset', ' the empty set ')
    expr = expr.replace(r'\varnothing', ' the empty set ')
    
    # Logic operators
    expr = expr.replace(r'\forall', ' for all ')
    expr = expr.replace(r'\exists', ' there exists ')
    expr = expr.replace(r'\land', ' and ')
    expr = expr.replace(r'\lor', ' or ')
    expr = expr.replace(r'\neg', ' not ')
    expr = expr.replace(r'\wedge', ' and ')
    expr = expr.replace(r'\vee', ' or ')
    
    # Text formatting in math mode
    expr = re.sub(r'\\text\{([^}]+)\}', r'\1', expr)
    expr = re.sub(r'\\mathrm\{([^}]+)\}', r'\1', expr)
    expr = re.sub(r'\\mathit\{([^}]+)\}', r'\1', expr)
    expr = re.sub(r'\\mathbf\{([^}]+)\}', r'\1', expr)
    expr = re.sub(r'\\mathcal\{([^}]+)\}', r'\1', expr)
    
    # Remove remaining LaTeX commands (generic cleanup)
    expr = re.sub(r'\\[a-zA-Z]+\*?', ' ', expr)
    
    # Clean up brackets and braces
    expr = expr.replace('{', '').replace('}', '')
    expr = expr.replace('\\left', '').replace('\\right', '')
    
    # Convert remaining math operators that might appear as text
    expr = expr.replace('*', ' times ')
    expr = expr.replace('+', ' plus ')
    expr = expr.replace('-', ' minus ')
    expr = expr.replace('/', ' divided by ')
    # Only replace = if not part of other operations
    if ' = ' in expr:
        expr = expr.replace(' = ', ' equals ')
    
    # Clean up extra spaces
    expr = re.sub(r'\s+', ' ', expr).strip()
    
    # Final pass: if there are still function-call-like patterns, describe them
    if re.search(r'[a-zA-Z_]+\([^)]+\)', expr):
        # There's still function notation - try to handle it generically
        expr = re.sub(r'([a-zA-Z_]+)\(([^)]+)\)', r'the \1 of \2', expr)
    
    return expr

def process_content_line(line):
    """Process a line of regular content (not a structural element)."""
    if not line.strip():
        return ""
    
    # Convert inline math $...$ to speech
    def replace_inline_math(match):
        math = match.group(1)
        speech = convert_math_expr_to_speech(math)
        # Add spaces around the converted math
        return ' ' + speech + ' '
    
    line = re.sub(r'\$([^\$]+)\$', replace_inline_math, line)
    
    # Remove any remaining $ signs
    line = line.replace('$', '')
    
    # Convert inline formatting
    line = re.sub(r'\\emph\{([^}]+)\}', r'*\1*', line)
    line = re.sub(r'\\textbf\{([^}]+)\}', r'**\1**', line)
    line = re.sub(r'\\textit\{([^}]+)\}', r'*\1*', line)
    line = re.sub(r'\\texttt\{([^}]+)\}', r'`\1`', line)
    line = re.sub(r'\\textrm\{([^}]+)\}', r'\1', line)
    line = re.sub(r'\\textsc\{([^}]+)\}', r'\1', line)
    
    # Convert quotes
    line = line.replace('``', '"').replace("''", '"')
    line = line.replace('`', '')
    
    # Convert dashes
    line = line.replace('---', '—').replace('--', '–')
    
    # Handle citations and references
    line = re.sub(r'\\cite\{[^}]+\}', '', line)
    line = re.sub(r'\\citep\{[^}]+\}', '', line)
    line = re.sub(r'\\citet\{[^}]+\}', '', line)
    line = re.sub(r'Theorem~?\\ref\{[^}]+\}', 'the theorem', line)
    line = re.sub(r'Chapter~?\\ref\{[^}]+\}', 'the chapter', line)
    line = re.sub(r'Section~?\\ref\{[^}]+\}', 'the section', line)
    line = re.sub(r'Definition~?\\ref\{[^}]+\}', 'the definition', line)
    line = re.sub(r'Example~?\\ref\{[^}]+\}', 'the example', line)
    line = re.sub(r'Lemma~?\\ref\{[^}]+\}', 'the lemma', line)
    line = re.sub(r'Proposition~?\\ref\{[^}]+\}', 'the proposition', line)
    line = re.sub(r'Corollary~?\\ref\{[^}]+\}', 'the corollary', line)
    line = re.sub(r'Figure~?\\ref\{[^}]+\}', 'the figure', line)
    line = re.sub(r'Table~?\\ref\{[^}]+\}', 'the table', line)
    line = re.sub(r'\\ref\{[^}]+\}', 'the reference', line)
    line = re.sub(r'~', ' ', line)
    
    # Remove spacing commands
    line = re.sub(r'\\qed', '', line)
    line = re.sub(r'\\qedhere', '', line)
    line = re.sub(r'\\noindent', '', line)
    line = re.sub(r'\\medskip', '', line)
    line = re.sub(r'\\smallskip', '', line)
    line = re.sub(r'\\bigskip', '', line)
    line = re.sub(r'\\vspace\*?\{[^}]+\}', '', line)
    line = re.sub(r'\\hspace\*?\{[^}]+\}', '', line)
    line = re.sub(r'\\[vhVH]fill', '', line)
    
    # Remove other common LaTeX commands
    line = re.sub(r'\\pagebreak', '', line)
    line = re.sub(r'\\newpage', '', line)
    line = re.sub(r'\\clearpage', '', line)
    
    # Handle special characters
    line = line.replace(r'\&', '&')
    line = line.replace(r'\%', '%')
    line = line.replace(r'\#', '#')
    line = line.replace(r'\_', '_')
    line = line.replace(r'\{', '{')
    line = line.replace(r'\}', '}')
    
    # Clean up extra spaces and normalize whitespace
    line = re.sub(r'\s+', ' ', line).strip()
    
    return line

def convert_latex_to_tts(content):
    """Main conversion function."""
    output = []
    
    # State tracking
    in_lstlisting = False
    in_tikzpicture = False
    in_figure = False
    in_math_block = False
    in_enumerate = False
    in_itemize = False
    enumerate_counter = 0
    
    lines = content.split('\n')
    i = 0
    
    while i < len(lines):
        line = lines[i].rstrip()
        
        # Skip lstlisting blocks entirely
        if '\\begin{lstlisting}' in line:
            in_lstlisting = True
            i += 1
            continue
        if '\\end{lstlisting}' in line:
            in_lstlisting = False
            i += 1
            continue
        if in_lstlisting:
            i += 1
            continue
        
        # Skip tikzpicture blocks
        if '\\begin{tikzpicture}' in line:
            in_tikzpicture = True
            i += 1
            continue
        if '\\end{tikzpicture}' in line:
            in_tikzpicture = False
            i += 1
            continue
        if in_tikzpicture:
            i += 1
            continue
        
        # Skip figure blocks
        if '\\begin{figure}' in line:
            in_figure = True
            i += 1
            continue
        if '\\end{figure}' in line:
            in_figure = False
            i += 1
            continue
        if in_figure:
            i += 1
            continue
        
        # Skip tabular and table environments
        if '\\begin{tabular}' in line or '\\begin{table}' in line:
            depth = 1
            i += 1
            while i < len(lines) and depth > 0:
                if '\\begin{' in lines[i]:
                    depth += 1
                if '\\end{' in lines[i]:
                    depth -= 1
                i += 1
            continue
        
        # Handle display math blocks - skip them
        if '\\begin{align' in line or '\\begin{equation' in line or '\\begin{gather' in line or line.strip() == '\\[':
            in_math_block = True
            i += 1
            continue
        if '\\end{align' in line or '\\end{equation' in line or '\\end{gather' in line or line.strip() == '\\]':
            in_math_block = False
            i += 1
            continue
        if in_math_block:
            i += 1
            continue
        
        # Skip comment lines
        if line.strip().startswith('%'):
            i += 1
            continue
        
        # Skip lines that are just labels
        if line.strip().startswith('\\label{') and line.strip().endswith('}'):
            i += 1
            continue
        
        # Remove labels from lines that have other content
        line = re.sub(r'\\label\{[^}]+\}', '', line)
        
        # Handle chapter
        if '\\chapter{' in line:
            match = re.search(r'\\chapter\{([^}]+)\}', line)
            if match:
                output.append(f"\n## Chapter: {match.group(1)}\n")
            i += 1
            continue
        
        # Handle section
        if '\\section{' in line:
            match = re.search(r'\\section\{([^}]+)\}', line)
            if match:
                output.append(f"\n### {match.group(1)}\n")
            i += 1
            continue
        
        # Handle subsection
        if '\\subsection{' in line:
            match = re.search(r'\\subsection\{([^}]+)\}', line)
            if match:
                output.append(f"\n#### {match.group(1)}\n")
            i += 1
            continue
        
        # Handle subsubsection
        if '\\subsubsection{' in line:
            match = re.search(r'\\subsubsection\{([^}]+)\}', line)
            if match:
                output.append(f"\n##### {match.group(1)}\n")
            i += 1
            continue
        
        # Handle epigraph - collect multiline
        if '\\epigraph{' in line:
            full_line = line
            brace_count = line.count('{') - line.count('}')
            while brace_count > 0 and i + 1 < len(lines):
                i += 1
                next_line = lines[i]
                full_line += ' ' + next_line.strip()
                brace_count += next_line.count('{') - next_line.count('}')
            
            match = re.search(r'\\epigraph\{([^}]+)\}\{([^}]+)\}', full_line)
            if match:
                quote = match.group(1).strip()
                author = match.group(2).strip()
                # Clean the quote and author
                quote = process_content_line(quote)
                author = process_content_line(author)
                output.append(f"\n> {quote}\n>\n> — {author}\n")
            i += 1
            continue
        
        # Handle theorem environments
        if '\\begin{theorem}' in line:
            title_match = re.search(r'\\begin\{theorem\}\[([^\]]+)\]', line)
            if title_match:
                output.append(f"\n**Theorem ({title_match.group(1)}):**\n")
            else:
                output.append("\n**Theorem:**\n")
            i += 1
            continue
        
        if '\\end{theorem}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle definition
        if '\\begin{definition}' in line:
            title_match = re.search(r'\\begin\{definition\}\[([^\]]+)\]', line)
            if title_match:
                output.append(f"\n**Definition ({title_match.group(1)}):**\n")
            else:
                output.append("\n**Definition:**\n")
            i += 1
            continue
        
        if '\\end{definition}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle proof
        if '\\begin{proof}' in line:
            output.append("\n**Proof:**\n")
            i += 1
            continue
        
        if '\\end{proof}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle corollary
        if '\\begin{corollary}' in line:
            title_match = re.search(r'\\begin\{corollary\}\[([^\]]+)\]', line)
            if title_match:
                output.append(f"\n**Corollary ({title_match.group(1)}):**\n")
            else:
                output.append("\n**Corollary:**\n")
            i += 1
            continue
        
        if '\\end{corollary}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle lemma
        if '\\begin{lemma}' in line:
            title_match = re.search(r'\\begin\{lemma\}\[([^\]]+)\]', line)
            if title_match:
                output.append(f"\n**Lemma ({title_match.group(1)}):**\n")
            else:
                output.append("\n**Lemma:**\n")
            i += 1
            continue
        
        if '\\end{lemma}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle proposition
        if '\\begin{proposition}' in line:
            title_match = re.search(r'\\begin\{proposition\}\[([^\]]+)\]', line)
            if title_match:
                output.append(f"\n**Proposition ({title_match.group(1)}):**\n")
            else:
                output.append("\n**Proposition:**\n")
            i += 1
            continue
        
        if '\\end{proposition}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle remark
        if '\\begin{remark}' in line:
            output.append("\n**Remark:**\n")
            i += 1
            continue
        
        if '\\end{remark}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle interpretation
        if '\\begin{interpretation}' in line:
            output.append("\n**Interpretation:**\n")
            i += 1
            continue
        
        if '\\end{interpretation}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle example
        if '\\begin{example}' in line:
            title_match = re.search(r'\\begin\{example\}\[([^\]]+)\]', line)
            if title_match:
                output.append(f"\n**Example ({title_match.group(1)}):**\n")
            else:
                output.append("\n**Example:**\n")
            i += 1
            continue
        
        if '\\end{example}' in line:
            output.append("\n")
            i += 1
            continue
        
        # Handle enumerate
        if '\\begin{enumerate}' in line:
            in_enumerate = True
            enumerate_counter = 0
            output.append("\n")
            i += 1
            continue
        
        if '\\end{enumerate}' in line:
            in_enumerate = False
            output.append("\n")
            i += 1
            continue
        
        # Handle itemize
        if '\\begin{itemize}' in line:
            in_itemize = True
            output.append("\n")
            i += 1
            continue
        
        if '\\end{itemize}' in line:
            in_itemize = False
            output.append("\n")
            i += 1
            continue
        
        # Handle items
        if '\\item' in line:
            item_text = line.replace('\\item', '').strip()
            item_text = process_content_line(item_text)
            if in_enumerate:
                enumerate_counter += 1
                output.append(f"{enumerate_counter}. {item_text}")
            else:
                output.append(f"* {item_text}")
            i += 1
            continue
        
        # Process regular content lines
        if line.strip():
            processed = process_content_line(line)
            if processed:
                output.append(processed)
        else:
            # Preserve blank lines for readability
            output.append("")
        
        i += 1
    
    return '\n'.join(output)

def main():
    input_file = '/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/tex_v2_chapters/idt_ch8_14.tex'
    output_file = '/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/_tts_ch8_14_part2.md'
    
    print("Reading LaTeX file...", file=sys.stderr)
    with open(input_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    print(f"Converting {len(content)} characters...", file=sys.stderr)
    
    # Add the Part II header
    result = "# Part II: Structure and Dynamics\n\n"
    result += convert_latex_to_tts(content)
    
    print(f"Writing {len(result)} characters to output...", file=sys.stderr)
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(result)
    
    print(f"✓ Conversion complete!", file=sys.stderr)
    print(f"✓ Output: {output_file}", file=sys.stderr)
    print(f"✓ Size: {len(result)} characters", file=sys.stderr)

if __name__ == '__main__':
    main()
