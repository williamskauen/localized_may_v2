import math
import os
import csv

def format_line(line):
    return f"   {line}\n"

def positive_line_height(ts):
    return positive_slope * ts + positive_constant_term

def negative_line_height(ts):
    return negative_slope * ts + negative_constant_term

def line_height(ts):
    return min(positive_line_height(ts), negative_line_height(ts))

def parse_name(name : str, full = False) -> str:
    if name == "":
        return ""
    new_name = ""
    name = name.replace("*", "")
    monomials = [string.strip() for string in name.split("+")]
    for monomial in monomials:
        variables = monomial.split("h")[1:]
        new_monomial = ""
        for variable in variables:
            i = variable[1]
            j = variable[3]
            if "n" in variable:
                if "^" in variable:
                    exponent = "^{-" + variable.split("^")[1] + "}"
                else:
                    exponent = "^{-1}"
            else:
                if "^" in variable:
                    exponent = "^{" + variable.split("^")[1] + "}"
                else:
                    exponent = ""
            variable = f"h_{{{i},{j}}}" + exponent + " "
            new_monomial += variable
        new_name += new_monomial + "+ "
    new_name = new_name[:-3]
    if not full:
        if "+" in new_name:
            new_name = new_name.split("+")[0] + "+ \\cdots"
    return new_name

if "homology_pictures" not in os.listdir():
    os.mkdir("homology_pictures")

if "homology_tables" not in os.listdir():
    os.mkdir("homology_tables")

os.chdir("homology_data")
data_files = os.listdir()
print("Select data file by typing the number matching the file: ")
for i, filename in enumerate(data_files):
    print(f"[{i + 1}] {filename}")

file_number = input()
data_file = data_files[int(file_number) - 1]

with open(data_file, "r") as f:
    csvreader = csv.reader(f)
    first_line = csvreader.__next__()
    second_line = csvreader.__next__()
    positive_slope = float(second_line[0])
    negative_slope = float(second_line[1])
    positive_constant_term = float(second_line[2])
    negative_constant_term = float(second_line[3])
    distance_to_line = round(float(second_line[4]), 2)
    localization_amount = int(second_line[5])
    page_number = int(second_line[6])
    signs = []
    if localization_amount >= 2:
        signs = 2*[-1]
    else:
        signs = localization_amount * [-1] + (2 - localization_amount) * [1]
    
    target_vars = ["h_{1,0}", "h_{1,1}"]
    
    homology_classes = []
    for line in csvreader:
        homology_class = {}
        data_fields = ["name", "ts_degree", "s_degree", "0_target", "1_target"]
        for i, field in enumerate(data_fields):
            if field == "ts_degree" or field == "s_degree":
                homology_class[field] = int(line[i])
            else:
                homology_class[field] = line[i]
        homology_classes.append(homology_class)

os.chdir("..")

def generate_picture_code(ts_start : int = 1, picture_width : int = 12, max_distance : float = None) -> str:
    if localization_amount == 0:
        picture_height = picture_width
    else:
        picture_height = int(max_distance + positive_slope * picture_width)
    classes_to_draw = []
    degrees_to_draw = []
    for homology_class in homology_classes:
        ts_degree = homology_class["ts_degree"]
        s_degree = homology_class["s_degree"]
        if ts_degree < ts_start or ts_degree > ts_start + picture_width - 2:
            continue
        if localization_amount == 0 and s_degree > ts_start + picture_width - 2:
            continue
        if max_distance != None and line_height(ts_degree) - s_degree > max_distance + 0.00001:
            continue
        classes_to_draw.append(homology_class)
        degrees_to_draw.append((ts_degree, s_degree))
    if localization_amount == 0:
        lowest_y = 0
    else:
        lowest_y = math.floor(line_height(ts_start - 1) - max_distance + 0.001) + 1 # + 1 since this will be one above corner position

    tikz_code = ["\\begin{tikzpicture}\n"]

    setup_lines = [f"\\draw[black, line width = 0.5mm] (0, 0) -- ({picture_width}, 0);", f"\\draw[black, line width = 0.5mm] (0, 0) -- (0, {picture_height});", f"\\node at ({picture_width / 2}, -1) {{$t - s$}};", f"\\node at (-1, {picture_height / 2}) {{$s$}};"]

    for i, j in zip(range(1, picture_width), range(ts_start, ts_start + picture_width - 1)):
        setup_lines.append(f"\\node at ({i}, -0.5) {{{j}}};")

    for i, j in zip(range(1, picture_height), range(lowest_y, lowest_y + picture_height - 1)):
        setup_lines.append(f"\\node at (-0.5, {i}) {{{j}}};")

    if localization_amount != 0:
        line_offset = line_height(ts_start - 1) - max_distance - lowest_y + 1
        setup_lines.append(f"\\draw[green, line width = 1mm] (0, {line_offset}) -- ({picture_width}, {positive_slope * picture_width + line_offset});")
        setup_lines.append(f"\\draw[red, line width = 1mm] (0, {max_distance + line_offset}) -- ({picture_width}, {positive_slope * picture_width + max_distance + line_offset});")

    for line in setup_lines:
        tikz_code.append(format_line(line))

    dot_drawn = []
    zero_drawn = []
    one_drawn = []

    for homology_class in classes_to_draw:
        name = homology_class["name"]
        ts_degree = homology_class["ts_degree"]
        s_degree = homology_class["s_degree"]
        zero_target = homology_class["0_target"]
        one_target = homology_class["1_target"]

        degree_pair = (ts_degree, s_degree)
        draw_ts = ts_degree - ts_start + 1
        draw_s = s_degree - lowest_y + 1
        draw_code = []

        if degree_pair not in dot_drawn:
            draw_code.append(f"\\filldraw[black] ({draw_ts}, {draw_s}) circle (1.5pt);")
            dot_drawn.append(degree_pair)

        if degree_pair not in zero_drawn and zero_target != "" and (ts_degree, s_degree + 1) in degrees_to_draw:
            draw_code.append(f"\\draw[->, black, thick] ({draw_ts}, {draw_s}) -- ({draw_ts}, {draw_s + 0.95});")
            zero_drawn.append(degree_pair)

        if degree_pair not in one_drawn and one_target != "" and (ts_degree + 1, s_degree + 1) in degrees_to_draw:
            draw_code.append(f"\\draw[->, black, thick] ({draw_ts}, {draw_s}) -- ({draw_ts + 0.95}, {draw_s + 0.95});")
            one_drawn.append(degree_pair)

        for line in draw_code:
            tikz_code.append(format_line(line))


    tikz_code.append("\\end{tikzpicture}")
    return tikz_code, ts_start, picture_width


def generate_table_code(ts_start : int = 1, ts_stop : int = 5, max_distance : int = None):
    classes_to_add = []

    for homology_class in homology_classes:
        ts_degree = homology_class["ts_degree"]
        s_degree = homology_class["s_degree"]
        if max_distance != None and line_height(ts_degree) - s_degree > max_distance + 0.00001:
            continue
        if ts_degree >= ts_start and ts_degree <= ts_stop:
            classes_to_add.append(homology_class)
    
    table_code = ["\\begin{tabular}{|c|c|c|c|c|}\n"]
    table_code.append(format_line("\\hline"))
    table_code.append(format_line(f"\\textbf{{Name}} & \\textbf{{ts}} & \\textbf{{s}} & $\\mathbf{{{target_vars[0]}}}$ & $\\mathbf{{{target_vars[1]}}}$ \\\\"))
    table_code.append(format_line("\\hline"))

    classes_to_add.sort(key = lambda x : (x["ts_degree"], x["s_degree"]))

    for homology_class in classes_to_add:
        name = homology_class["name"]
        ts_degree = homology_class["ts_degree"]
        s_degree = homology_class["s_degree"]
        zero_target = homology_class["0_target"]
        one_target = homology_class["1_target"]
        table_row = f"${parse_name(name)} $ & ${ts_degree} $ & ${s_degree} $ & ${parse_name(zero_target)} $ & ${parse_name(one_target)} $ \\\\"
        table_code.append(format_line(table_row))
        table_code.append(format_line("\\hline"))
    
    table_code.append("\\end{tabular}")
    return table_code, ts_start, ts_stop


mode = input("Choose mode. Type 1 for picture and 2 for table: ")
if mode == "1":
    ts_start = input("Type desired ts start value (leave blank for default of 1): ")
    if ts_start == "":
        ts_start = 1
    else:
        ts_start = int(ts_start)
    max_distance_to_line = input("Type desired max distance from line to plot (leave blank to include everything): ")
    if max_distance_to_line == "":
        max_distance_to_line = distance_to_line
    else:
        max_distance_to_line = float(max_distance_to_line)
    code, ts_start, picture_width = generate_picture_code(ts_start, max_distance = max_distance_to_line)
    filename = f"homology_tikz_l-{localization_amount}_p-{page_number}_d-{max_distance_to_line}_ts-{ts_start}-{ts_start + picture_width - 1}.txt"
    os.chdir("homology_pictures")
elif mode == "2":
    ts_start = input("Type desired ts start value (leave blank for default of 1): ")
    if ts_start == "":
        ts_start = 1
    else:
        ts_start = int(ts_start)
    ts_stop = input("Type desired ts stop value (leave blank for default of 11): ")
    if ts_stop == "":
        ts_stop = 11
    else:
        ts_stop = int(ts_stop)
    max_distance_to_line = input("Type desired max distance from line to plot (leave blank to include everything): ")
    if max_distance_to_line == "":
        max_distance_to_line = distance_to_line
    else:
        max_distance_to_line = float(max_distance_to_line)
    code, ts_start, picture_width = generate_table_code(ts_start, ts_stop, max_distance = max_distance_to_line)
    filename = f"homology_table_l-{localization_amount}_p-{page_number}_d-{max_distance_to_line}_ts-{ts_start}-{ts_stop}.txt"
    os.chdir("homology_tables")
else:
    raise ValueError("Invalid mode")


write_data = True
if filename in os.listdir():
    overwrite = input("Code file with equivalent parameters alreadly present, do you wish to overwrite? [y/n]: ")
    if overwrite != "y":
        write_data = False
    else:
        os.remove(filename)

if write_data:
    with open(filename, "w") as f:
        for line in code:
            f.write(line)