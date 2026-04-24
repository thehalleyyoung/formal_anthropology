import re
import sys

def convert_math_to_speech(text):
    """Convert mathematical notation to speakable English."""
    
    # First pass: Handle display math blocks - replace with prose description
    # We need to describe what the math says, not preserve it
    text = re.sub(r'\\\[.*?\\\]', ' [mathematical expression omitted for speech] ', text, flags=re.DOTALL)
    text = re.sub(r'\\begin\{align\*?\}.*?\\end\{align\*?\}', ' [mathematical expression omitted for speech] ', text, flags=re.DOTALL)
    text = re.sub(r'\\begin\{equation\*?\}.*?\\end\{equation\*?\}', ' [mathematical expression omitted for speech] ', text, flags=re.DOTALL)
    
    # Inline math - try to convert simple ones
    def convert_inline_math(match):
        math = match.group(1)
        
        # Simple patterns
        math = math.replace('\\IS', 'the ideatic space')
        math = math.replace('\\mathcal{I}', 'the ideatic space')
        math = math.replace('\\R', 'the real numbers')
        math = math.replace('\\mathbb{R}', 'the real numbers')
        math = math.replace('\\N', 'the natural numbers')
        math = math.replace('\\mathbb{N}', 'the natural numbers')
        math = math.replace('\\void', 'the void')
        math = math.replace('\\varepsilon', 'the void')
        math = math.replace('\\emerge', 'emergence')
        math = math.replace('\\kappa', 'emergence')
        math = math.replace('\\compose', 'composed with')
        math = math.replace('\\circ', 'composed with')
        math = math.replace('\\rs', 'the resonance')
        
        # Remove remaining LaTeX commands
        math = re.sub(r'\\[a-zA-Z]+', '', math)
        
        # If it's still too mathy, describe it generically
        if any(c in math for c in ['$', '{', '}', '^', '_', '\\']]):
            return ' [mathematical expression] '
        
        return ' ' + math.strip() + ' '
    
    text = re.sub(r'\$([^\$]+)\$', convert_inline_math, text)
    
    # Remove any remaining $ signs
    text = text.replace('$', '')
    
    return text

def process_line(line):
    """Process a single line, converting LaTeX to TTS markdown."""
    # Skip empty lines
    if not line.strip():
        return ""
    
    # Remove \label commands
    line = re.sub(r'\\label\{[^}]+\}', '', line)
    
    # Handle environments
    # Definition
    if '\\begin{definition}' in line:
        title_match = re.search(r'\\begin\{definition\}\[([^\]]+)\]', line)
        if title_match:
            return f"\n**Definition ({title_match.group(1)}):**\n"
        else:
            return "\n**Definition:**\n"
    
    if '\\end{definition}' in line:
        return "\n"
    
    # Theorem
    if '\\begin{theorem}' in line:
        title_match = re.search(r'\\begin\{theorem\}\[([^\]]+)\]', line)
        if title_match:
            return f"\n**Theorem ({title_match.group(1)}):**\n"
        else:
            return "\n**Theorem:**\n"
    
    if '\\end{theorem}' in line:
        return "\n"
    
    # Proof
    if '\\begin{proof}' in line:
        return "\n**Proof:**\n"
    
    if '\\end{proof}' in line:
        return "\n"
    
    # Corollary
    if '\\begin{corollary}' in line:
        title_match = re.search(r'\\begin\{corollary\}\[([^\]]+)\]', line)
        if title_match:
            return f"\n**Corollary ({title_match.group(1)}):**\n"
        else:
            return "\n**Corollary:**\n"
    
    if '\\end{corollary}' in line:
        return "\n"
    
    # Lemma
    if '\\begin{lemma}' in line:
        title_match = re.search(r'\\begin\{lemma\}\[([^\]]+)\]', line)
        if title_match:
            return f"\n**Lemma ({title_match.group(1)}):**\n"
        else:
            return "\n**Lemma:**\n"
    
    if '\\end{lemma}' in line:
        return "\n"
    
    # Proposition
    if '\\begin{proposition}' in line:
        title_match = re.search(r'\\begin\{proposition\}\[([^\]]+)\]', line)
        if title_match:
            return f"\n**Proposition ({title_match.group(1)}):**\n"
        else:
            return "\n**Proposition:**\n"
    
    if '\\end{proposition}' in line:
        return "\n"
    
    # Remark
    if '\\begin{remark}' in line:
        return "\n**Remark:**\n"
    
    if '\\end{remark}' in line:
        return "\n"
    
    # Interpretation
    if '\\begin{interpretation}' in line:
        return "\n**Interpretation:**\n"
    
    if '\\end{interpretation}' in line:
        return "\n"
    
    # Example
    if '\\begin{example}' in line:
        title_match = re.search(r'\\begin\{example\}\[([^\]]+)\]', line)
        if title_match:
            return f"\n**Example ({title_match.group(1)}):**\n"
        else:
            return "\n**Example:**\n"
    
    if '\\end{example}' in line:
        return "\n"
    
    # Skip display math delimiters
    if line.strip() in ['\\[', '\\]']:
        return ""
    
    # Convert math first
    line = convert_math_to_speech(line)
    
    # Convert inline formatting
    line = re.sub(r'\\emph\{([^}]+)\}', r'*\1*', line)
    line = re.sub(r'\\textbf\{([^}]+)\}', r'**\1**', line)
    line = re.sub(r'\\textit\{([^}]+)\}', r'*\1*', line)
    line = re.sub(r'\\texttt\{([^}]+)\}', r'`\1`', line)
    
    # Convert citations - simplify
    line = re.sub(r'\\cite\{[^}]+\}', '', line)
    line = re.sub(r'\\ref\{[^}]+\}', 'the referenced result', line)
    line = re.sub(r'Theorem~\\ref\{[^}]+\}', 'the theorem', line)
    line = re.sub(r'Chapter~\\ref\{[^}]+\}', 'an earlier chapter', line)
    line = re.sub(r'Section~\\ref\{[^}]+\}', 'the section', line)
    
    # Remove remaining LaTeX commands
    line = re.sub(r'\\qed', '', line)
    line = re.sub(r'\\qedhere', '', line)
    line = re.sub(r'\\noindent', '', line)
    line = re.sub(r'\\medskip', '', line)
    line = re.sub(r'\\smallskip', '', line)
    line = re.sub(r'\\bigskip', '', line)
    
    # Clean up extra spaces
    line = re.sub(r'\s+', ' ', line).strip()
    
    return line

def convert_latex_to_tts(content):
    """Convert LaTeX content to TTS-optimized markdown."""
    output = []
    in_lstlisting = False
    in_tikzpicture = False
    in_figure = False
    in_math_block = False
    
    lines = content.split('\n')
    i = 0
    
    while i < len(lines):
        line = lines[i].rstrip()
        
        # Handle lstlisting blocks - skip entirely
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
        
        # Handle tikzpicture blocks - skip entirely
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
        
        # Handle figure blocks - skip entirely
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
        
        # Handle multi-line math blocks
        if '\\begin{align' in line or '\\begin{equation' in line or line.strip() == '\\[':
            in_math_block = True
            i += 1
            continue
        if '\\end{align' in line or '\\end{equation' in line or line.strip() == '\\]':
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
        
        # Chapter
        if '\\chapter{' in line:
            match = re.search(r'\\chapter\{([^}]+)\}', line)
            if match:
                chapter_name = match.group(1)
                # Try to extract chapter number if present
                output.append(f"\n## Chapter: {chapter_name}\n")
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
        
        # Subsubsection
        if '\\subsubsection{' in line:
            match = re.search(r'\\subsubsection\{([^}]+)\}', line)
            if match:
                output.append(f"\n##### {match.group(1)}\n")
            i += 1
            continue
        
        # Epigraph - handle multi-line
        if '\\epigraph{' in line:
            full_line = line
            brace_count = line.count('{') - line.count('}')
            while brace_count > 0 and i + 1 < len(lines):
                i += 1
                next_line = lines[i]
                full_line += ' ' + next_line
                brace_count += next_line.count('{') - next_line.count('}')
            
            # Try to extract quote and author
            match = re.search(r'\\epigraph\{([^}]+)\}\{([^}]+)\}', full_line)
            if match:
                quote = match.group(1).strip()
                author = match.group(2).strip()
                output.append(f"\n> {quote}\n>\n> — {author}\n")
            i += 1
            continue
        
        # Process the line
        processed = process_line(line)
        if processed:
            output.append(processed)
        
        i += 1
    
    return '\n'.join(output)

# Main execution
if __name__ == '__main__':
    print("Reading source file...", file=sys.stderr)
    with open('/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/tex_v2_chapters/idt_ch8_14.tex', 'r', encoding='utf-8') as f:
        content = f.read()
    
    print("Converting to TTS markdown...", file=sys.stderr)
    result = "# Part II: Structure and Dynamics\n\n" + convert_latex_to_tts(content)
    
    print(f"Writing output ({len(result)} characters)...", file=sys.stderr)
    with open('/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/_tts_ch8_14_part2.md', 'w', encoding='utf-8') as f:
        f.write(result)
    
    print("Conversion complete!", file=sys.stderr)
    print(f"Output written to: /Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/_tts_ch8_14_part2.md", file=sys.stderr)

