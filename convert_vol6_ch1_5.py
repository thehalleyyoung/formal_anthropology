#!/usr/bin/env python3
"""
Convert vol6_ch1_5.tex to TTS-optimized markdown.
NO equations, NO code blocks, ALL content converted to flowing prose.
"""

import re
import sys

def convert_latex_to_markdown(latex_content):
    """Convert LaTeX to TTS-optimized markdown."""
    output = []
    lines = latex_content.split('\n')
    i = 0
    in_lstlisting = False
    skip_to_end = False
    
    while i < len(lines):
        line = lines[i]
        
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
            
        # Skip comments and LaTeX directives
        if line.strip().startswith('%'):
            i += 1
            continue
            
        # Chapter
        if '\\chapter{' in line:
            match = re.search(r'\\chapter\{(.+?)\}', line)
            if match:
                output.append(f"\n## {match.group(1)}\n")
            i += 1
            continue
            
        # Section
        if '\\section{' in line:
            match = re.search(r'\\section\{(.+?)\}', line)
            if match:
                output.append(f"\n### {match.group(1)}\n")
            i += 1
            continue
            
        # Subsection
        if '\\subsection{' in line:
            match = re.search(r'\\subsection\{(.+?)\}', line)
            if match:
                output.append(f"\n#### {match.group(1)}\n")
            i += 1
            continue
            
        # Epigraph
        if '\\epigraph{' in line:
            # Collect multi-line epigraph
            epigraph_lines = [line]
            while i < len(lines) - 1 and '}' not in lines[i]:
                i += 1
                epigraph_lines.append(lines[i])
            full_epigraph = ' '.join(epigraph_lines)
            match = re.search(r'\\epigraph\{(.+?)\}\{(.+?)\}', full_epigraph, re.DOTALL)
            if match:
                quote = match.group(1).replace('``', '"').replace("''", '"')
                attr = match.group(2).replace('---', '—').replace('\\emph{', '*').replace('}', '*')
                output.append(f"\n> {quote}\n> {attr}\n")
            i += 1
            continue
            
        # Labels
        if '\\label{' in line:
            i += 1
            continue
            
        # Environments
        if '\\begin{definition}' in line or '\\begin{theorem}' in line or '\\begin{lemma}' in line or '\\begin{proposition}' in line or '\\begin{corollary}' in line:
            env_type = re.search(r'\\begin\{(\w+)\}', line).group(1)
            # Collect content until \end{...}
            env_content = []
            i += 1
            while i < len(lines) and f'\\end{{{env_type}}}' not in lines[i]:
                env_content.append(lines[i])
                i += 1
            # Process environment content
            text = process_environment_text('\n'.join(env_content))
            output.append(f"\n**{env_type.title()}:** {text}\n")
            i += 1
            continue
            
        if '\\begin{proof}' in line:
            env_content = []
            i += 1
            while i < len(lines) and '\\end{proof}' not in lines[i]:
                env_content.append(lines[i])
                i += 1
            text = process_environment_text('\n'.join(env_content))
            output.append(f"\n**Proof:** {text}\n")
            i += 1
            continue
            
        if '\\begin{interpretation}' in line or '\\begin{remark}' in line or '\\begin{example}' in line:
            env_type = re.search(r'\\begin\{(\w+)\}', line).group(1)
            env_content = []
            i += 1
            while i < len(lines) and f'\\end{{{env_type}}}' not in lines[i]:
                env_content.append(lines[i])
                i += 1
            text = process_environment_text('\n'.join(env_content))
            output.append(f"\n**{env_type.title()}:** {text}\n")
            i += 1
            continue
            
        # Skip math environments
        if '\\[' in line or '\\begin{align' in line or '\\begin{equation' in line:
            # Find the closing
            if '\\]' not in line:
                while i < len(lines) and '\\]' not in lines[i] and '\\end{align' not in lines[i] and '\\end{equation' not in lines[i]:
                    i += 1
            i += 1
            continue
            
        # Process regular text lines
        processed = process_text_line(line)
        if processed and processed.strip():
            output.append(processed)
        
        i += 1
    
    return '\n'.join(output)

def process_environment_text(text):
    """Process text within an environment, converting math to prose."""
    # This is a simplified version - full conversion would need more sophisticated parsing
    text = convert_math_to_prose(text)
    text = text.replace('\\textbf{', '**').replace('}', '**')
    text = text.replace('\\emph{', '*').replace('}', '*')
    text = text.replace('\\textit{', '*').replace('}', '*')
    return text.strip()

def process_text_line(line):
    """Process a regular text line."""
    if not line.strip() or line.strip().startswith('%'):
        return ''
    
    # Convert common LaTeX formatting
    line = line.replace('\\textbf{', '**').replace('}', '**')
    line = line.replace('\\emph{', '*').replace('}', '*')
    line = line.replace('\\textit{', '*').replace('}', '*')
    line = line.replace('``', '"').replace("''", '"')
    line = line.replace('---', '—').replace('--', '–')
    
    # Remove inline math (simple version)
    line = re.sub(r'\$[^\$]+\$', '[MATH]', line)
    
    return line

def convert_math_to_prose(text):
    """Convert mathematical notation to natural language prose."""
    # This is a placeholder - the actual implementation would be quite complex
    # For now, just strip math delimiters
    text = re.sub(r'\$[^\$]+\$', '[MATH EXPRESSION]', text)
    text = re.sub(r'\\\[.*?\\\]', '[MATH EQUATION]', text, flags=re.DOTALL)
    return text

if __name__ == '__main__':
    input_file = '/Users/halleyyoung/Documents/beatingSOTAcopilot/formal_anthropology/tex_v2_chapters/vol6_ch1_5.tex'
    
    with open(input_file, 'r', encoding='utf-8') as f:
        latex_content = f.read()
    
    markdown = convert_latex_to_markdown(latex_content)
    print(markdown)

