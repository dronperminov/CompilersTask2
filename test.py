import os

def parse_answer(path):
	with open(path) as f:
		lines = f.read().splitlines()

	blocks = []

	for line in lines:
		if line.startswith("export function") or line.endswith("}"):
			continue

		if line[0] == "@":
			blocks.append({ "name" : line, "instructions": [] })
		else:
			blocks[-1]["instructions"].append(line.lstrip(" \t").rstrip(" \t"))

	return blocks

def test(answers_path, outputs_path):
	answers = parse_answer(answers_path)
	outputs = parse_answer(outputs_path)

	if len(answers) != len(outputs):
		print("Different number of blocks")
		return False

	answer_blocks = set()
	output_blocks = set()

	for block in answers:
		answer_blocks.add(block["name"])

	for block in outputs:
		output_blocks.add(block["name"])

	if answer_blocks != output_blocks:
		print("Different block sets")
		return False

	for i in range(len(answers)):
		if len(answers[i]["instructions"]) != len(outputs[i]["instructions"]):
			print("Different number of instructions at block '" + answers[i]["name"] + "'")
			return False

		for j in range(len(answers[i]["instructions"])):
			if (answers[i]["instructions"][j] != outputs[i]["instructions"][j]):
				print("Different instructions at block '" + answers[i]["name"] + "'")
				return False

	return True

answer_path = "answers/"
output_path = "outputs/"

n = len(os.listdir("tests"))

for i in range(n):
	answer_file = answer_path + str(i + 1) + '.txt'
	output_file = output_path + str(i + 1) + '.txt'

	print("Test " + str(i + 1) + ': ', end='')

	if test(answer_file, output_file):
		print("OK")
	else:
		print("\nCorrect:")
		os.system("cat " + answer_file)

		print("\nOutput:")
		os.system("cat " + output_file)
