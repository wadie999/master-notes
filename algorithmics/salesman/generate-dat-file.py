def create_dat_file(file_path, output_file_path):
    with open(file_path, 'r') as file:
        contents = file.readlines()

    # Extracting the number of cities
    num_cities = int(contents[0].strip())

    # Preparing data for x and y coordinates
    x_coords = []
    y_coords = []
    for line in contents[1:]:
        _, x, y = line.split()
        x_coords.append(x)
        y_coords.append(y)

    # Creating .dat file content
    dat_content = "param x :=\n"
    for i, x in enumerate(x_coords, start=1):
        dat_content += f'<"{i}"> {x},\n'

    dat_content += ";\n\nparam y :=\n"
    for i, y in enumerate(y_coords, start=1):
        dat_content += f'<"{i}"> {y},\n'

    dat_content += ";\n"

    # Writing to the output file
    with open(output_file_path, 'w') as file:
        file.write(dat_content)

    return output_file_path



# Example usage
file_path = '/home/wadie/Desktop/m1-iafa/algorithmics/salesman/tsp5.txt'
output_dat_file_path = 'tsp5.dat'
create_dat_file(file_path, output_dat_file_path)

file_path = '/home/wadie/Desktop/m1-iafa/algorithmics/salesman/tsp25.txt'
output_dat_file_path = 'tsp25.dat'
create_dat_file(file_path, output_dat_file_path)

file_path = '/home/wadie/Desktop/m1-iafa/algorithmics/salesman/tsp50.txt'
output_dat_file_path = 'tsp50.dat'
create_dat_file(file_path, output_dat_file_path)

file_path = '/home/wadie/Desktop/m1-iafa/algorithmics/salesman/tsp101.txt'
output_dat_file_path = 'tsp101.dat'
create_dat_file(file_path, output_dat_file_path)