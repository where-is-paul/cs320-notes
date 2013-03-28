from os import listdir, getcwd
from os.path import isfile, join

def datesorter(date):
    months = ["jan", "Feb", "March", "April"]
    datesplit = date.split()
    month = datesplit[0]
    day = datesplit[1].split(".")[0]

    idx1 = months.index(month)
    idx2 = int(day)

    return idx1*30 + idx2

path = join(getcwd(), "classnotes")
txtfiles = [ f for f in listdir(path) \
              if f.endswith('.txt') ]

txtfiles.sort(key=datesorter)

readme = open("README.md", 'w')
readme.write("cs320-notes\n")
readme.write("===========\n")
readme.write("\n")

for filename in txtfiles:
    ufile = open(join(path, filename))

    name = filename.split('.')[0]
    readme.write(name + "\n" + len(name)*"=" + "\n") 
    for line in ufile.readlines():
        readme.write(line)
    readme.write("\n\n")
    ufile.close()
    
readme.close()
    
