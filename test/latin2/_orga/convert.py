import json

def convert_jsonl_to_md(jsonl_path, md_path):
    with open(jsonl_path, 'r', encoding='utf-8') as f_in, open(md_path, 'w', encoding='utf-8') as f_out:
        f_out.write('# Kiro Chat Session Transcript\n\n')
        
        for line in f_in:
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
                
                # Format 1: Handles historical session metadata arrays (session.json format)
                if 'history' in data:
                    for turn in data['history']:
                        msg = turn.get('message', {})
                        role = msg.get('role')
                        content = msg.get('content', '')
                        
                        if role in ['user', 'assistant']:
                            display_role = '**User**' if role == 'user' else '**Kiro Extension Agent**'
                            if isinstance(content, list):
                                text_parts = [item.get('text', '') for item in content if item.get('type') == 'text']
                                content = '\n'.join(text_parts)
                            f_out.write(f'### {display_role}\n\n{content}\n\n---\n\n')
                    continue
                
                # Format 2: Handles live operational text messages (messages.jsonl stream)
                payload = data.get('payload', {})
                if isinstance(payload, dict):
                    msg_type = payload.get('type')
                    if msg_type in ['user', 'assistant']:
                        display_role = '**User**' if msg_type == 'user' else '**Kiro Extension Agent**'
                        content = payload.get('content', '')
                        if content:
                            f_out.write(f'### {display_role}\n\n{content}\n\n---\n\n')
            except Exception:
                # Silently bypass non-chat event logs (tool calls, environment configurations)
                continue

if __name__ == '__main__':
    convert_jsonl_to_md('messages.jsonl', 'chat_history.md')
    print('Markdown transcript created successfully!')