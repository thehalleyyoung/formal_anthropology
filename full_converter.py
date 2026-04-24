#!/usr/bin/env python3
"""
Complete converter for vol6_ch1_5.tex to TTS-optimized markdown.
Handles ALL mathematical notation conversion to natural language.
"""

import re
import sys

# Math-to-prose conversion mappings
MATH_CONVERSIONS = {
    r'\\rs\{([^}]+)\}\{([^}]+)\}': r'the resonance of \1 with \2',
    r'\\mathrm\{rs\}\s*\(([^,]+),\s*([^)]+)\)': r'the resonance of \1 with \2',
    r'\\emerge\{([^}]+)\}\{([^}]+)\}\{([^}]+)\}': r'the emergence of \1 and \2 as observed by \3',
    r'\\emerge\(([^,]+),\s*([^,]+),\s*([^)]+)\)': r'the emergence of \1 and \2 as observed by \3',
    r'\\kappa\(([^,]+),\s*([^,]+),\s*([^)]+)\)': r'the emergence of \1 and \2 as observed by \3',
    r'\\compose': r' composed with ',
    r'\\circ': r' composed with ',
    r'\\weight\{([^}]+)\}': r'the weight of \1',
    r'\\charge\{([^}]+)\}': r'the semantic charge of \1',
    r'\\totalE\{([^}]+)\}\{([^}]+)\}': r'the total emergence of \1 and \2',
    r'\\totalE\(([^,]+),\s*([^)]+)\)': r'the total emergence of \1 and \2',
    r'\\energy\{([^}]+)\}': r'the emergence energy of \1',
    r'\\enrich\{([^}]+)\}\{([^}]+)\}': r'the enrichment gap of \1 and \2',
    r'\\enrich\(([^,]+),\s*([^)]+)\)': r'the enrichment gap of \1 and \2',
    r'\\curv\{([^}]+)\}\{([^}]+)\}\{([^}]+)\}': r'the curvature at \1, \2, \3',
    r'\\curv\(([^,]+),\s*([^,]+),\s*([^)]+)\)': r'the curvature at \1, \2, \3',
    r'\\mathcal\{K\}\(([^,]+),\s*([^,]+),\s*([^)]+)\)': r'the curvature at \1, \2, \3',
    r'\\void': r'the void idea',
    r'\\IS': r'the ideatic space',
    r'\\R': r'the real numbers',
    r'\\N': r'the natural numbers',
    r'\\leq': r' is less than or equal to ',
    r'\\geq': r' is greater than or equal to ',
    r'\\neq': r' is not equal to ',
    r'\\forall': r'for every',
    r'\\exists': r'there exists',
    r'\\in': r' in ',
    r'\\to': r' maps to ',
    r'\\times': r' cross ',
    r'\\sqrt\{([^}]+)\}': r'the square root of \1',
    r'\|([^|]+)\|': r'the absolute value of \1',
}

def convert_math_inline(text):
    """Convert inline math $...$ to prose."""
    def replace_math(match):
        math = match.group(1)
        # Apply conversions
        for pattern, repl in MATH_CONVERSIONS.items():
            math = re.sub(pattern, repl, math)
        # Remove remaining LaTeX commands
        math = re.sub(r'\\[a-zA-Z]+\{([^}]+)\}', r'\1', math)
        math = re.sub(r'\\[a-zA-Z]+', '', math)
        # Clean up spacing
        math = re.sub(r'\s+', ' ', math).strip()
        return math
    
    # Handle $...$ 
    text = re.sub(r'\$([^\$]+)\$', replace_math, text)
    return text

def convert_math_display(text):
    """Convert display math to prose description."""
    # For display math, we'll return a prose version
    # This is simplified - full version would parse the math tree
    for pattern, repl in MATH_CONVERSIONS.items():
        text = re.sub(pattern, repl, text)
    text = re.sub(r'\\[a-zA-Z]+\{([^}]+)\}', r'\1', text)
    text = re.sub(r'\\[a-zA-Z]+', '', text)
    text = re.sub(r'\s+', ' ', text).strip()
    return text

def process_epigraph(lines, start_idx):
    """Extract and format epigraph."""
    text = ' '.join(lines[start_idx:start_idx+3])
    match = re.search(r'\\epigraph\{``(.+?)''\}\s*\{---([^,]+),\s*\\emph\{([^}]+)\}', text)
    if match:
        quote, author, work = match.groups()
        return f"\n> {quote}\n> —{author}, *{work}*\n", start_idx + 3
    return "", start_idx + 1

def convert_latex_file(input_file):
    """Main conversion function."""
    with open(input_file, 'r', encoding='utf-8') as f:
        lines = [line.rstrip() for line in f.readlines()]
    
    output = []
    i = 0
    in_lstlisting = False
    in_math_display = False
    
    while i < len(lines):
        line = lines[i]
        
        # Skip code blocks entirely
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
        
        # Skip display math blocks
        if '\\[' in line or '\\begin{align' in line or '\\begin{equation' in line:
            in_math_display = True
            i += 1
            continue
        if '\\]' in line or '\\end{align' in line or '\\end{equation' in line:
            in_math_display = False
            i += 1
            continue
        if in_math_display:
            i += 1
            continue
        
        # Skip comments and directives
        if line.strip().startswith('%') or line.strip().startswith('\\label'):
            i += 1
            continue
        
        # Chapter
        if '\\chapter{' in line:
            match = re.search(r'\\chapter\{([^}]+)\}', line)
            if match:
                output.append(f"\n## {match.group(1)}\n")
            i += 1
            continue
        
        # Section
        if '\\section{' in line:
            match = re.search(r'\\section\{([^}]+)\}', line)
            if match:
                output.append(f"\n### {match.group(1)}\n")
            i += 1
            continue
        
        # Subsection
        if '\\subsection{' in line:
            match = re.search(r'\\subsection\{([^}]+)\}', line)
            if match:
                output.append(f"\n#### {match.group(1)}\n")
            i += 1
            continue
        
        # Epigraph
        if '\\epigraph{' in line:
            epigraph, new_i = process_epigraph(lines, i)
            output.append(epigraph)
            i = new_i
            continue
        
        # Environments
        env_match = re.match(r'\\begin\{(definition|theorem|lemma|proposition|corollary|axiom_def|example|remark|interpretation|proof)\}', line)
        if env_match:
            env_name = env_match.group(1)
            env_lines = []
            i += 1
            # Collect until \end{env}
            while i < len(lines) and f'\\end{{{env_name}}}' not in lines[i]:
                if not lines[i].strip().startswith('\\label'):
                    env_lines.append(lines[i])
                i += 1
            
            # Process content
            env_text = '\n'.join(env_lines)
            env_text = convert_math_inline(env_text)
            env_text = env_text.replace('\\textbf{', '**').replace('\\emph{', '*').replace('\\textit{', '*')
            env_text = re.sub(r'\}', '', env_text)  # Remove remaining braces (simplified)
            env_text = env_text.replace('``', '"').replace("''", '"')
            env_text = env_text.replace('---', '—').replace('--', '–')
            env_text = env_text.replace('~', ' ')
            
            # Format output
            if env_name == 'proof':
                output.append(f"\n**Proof:** {env_text}\n")
            else:
                output.append(f"\n**{env_name.title().replace('_', ' ')}:** {env_text}\n")
            
            i += 1
            continue
        
        # Regular text
        if line.strip() and not line.strip().startswith('\\'):
            text = convert_math_inline(line)
            text = text.replace('\\textbf{', '**').replace('\\emph{', '*').replace('\\textit{', '*')
            text = text.replace('``', '"').replace("''", '"')
            text = text.replace('---', '—').replace('--', '–')
            text = text.replace('~', ' ')
            text = re.sub(r'\\[a-zA-Z]+\{([^}]+)\}', r'\1', text)
            output.append(text)
        
        i += 1
    
    return '\n'.join(output)

if __name__ == '__main__':
    input_file = sys.argv[1] if len(sys.argv) > 1 else '/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/tex_v2_chapters/vol6_ch1_5.tex'
    result = convert_latex_file(input_file)
    print(result)
