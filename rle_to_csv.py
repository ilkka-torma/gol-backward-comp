import sys

if __name__ == "__main__":
    in_name = sys.argv[1]
    with open(in_name, 'r') as f:
        lines = f.readlines()

    _, _, width_s, _, _, height_s, *_ = lines[0].split()
    width = int(width_s[:-1])
    height = int(height_s[:-1])
    s = ""
    x = 0
    y = 0
    string = ''.join(line.strip() for line in lines[1:])
    while string:
        i = 0
        while string[i] in "0123456789":
            i += 1
        if i:
            num = int(string[:i])
        else:
            num = 1
        
        if string[i] in '.AB':
            st = str('.AB'.index(string[i]))
            s += st*num
            x += num
            string = string[i+1:]
        elif string[i] == '!':
            break
        elif string[i] == '$':
            for _ in range(num):
                s += '0'*(width - x) + '\n'
                x = 0
                y += 1
            string = string[i+1:]
        else:
            print("Bad symbol:", string[i])
            quit()
    for _ in range(height-y):
        s += '0'*(width - x) + '\n'
        x = 0

    out_name = sys.argv[2]
    with open(out_name, 'w') as f:
        f.write(s)
