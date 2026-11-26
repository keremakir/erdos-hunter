import urllib.request, re

# 1. Brouwer Andw.html d=4 table
html = urllib.request.urlopen("https://aeb.win.tue.nl/codes/Andw.html", timeout=15).read().decode("utf-8", "ignore")
idx = html.find('name="d4"')
if idx == -1:
    idx = html.find('id="d4"')
if idx == -1:
    idx = html.find("A(n,4,w)")
print("Found d4 at:", idx)
sub = html[idx:idx+45000]
end = sub.find("d=6")
if end > 100:
    sub = sub[:end]
rows = re.findall(r"<tr.*?</tr>", sub, flags=re.S)
for r in rows:
    cells = [re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", c)).strip() for c in re.findall(r"<t[dh].*?</t[dh]>", r, flags=re.S)]
    if cells:
        print(" | ".join(cells))
