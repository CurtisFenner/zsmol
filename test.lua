-- Test script for the Smol compiler.
-- To run all tests,
--         lua test.lua

-- usage:
--         lua test.lua <query>
-- if <query> is blank, all tests are run.
-- if <query> begins with -, only negative tests are run.
-- if <query> begins with +, only positive tests are run.
-- if <query> contains text after an (optional) initial + or -, only tests whose
--     names contain the query string are run.

-- For example, to run all verification tests that the compiler should reject,
--         lua test.lua -verify

--------------------------------------------------------------------------------

-- ENVIRONMENT REQUIREMENTS

-- `ls` must be a utility available in the shell that lists file names in a
-- directory, one per line.

--- `diff` must be a utility available in the shell that compares text files.

-- Searches the current directory for folders named `tests/positive` and
-- `tests/negative`.

-- `tests/positive` should contain one or more folders; each is a test-category.
-- Each test category should contain one or more folders; each is a test-case.
-- Each positive test-case should contain:
-- + `out.correct`, the text that the test case should generate on standard
--   output
-- + `test.smol`, a test file in the `testing` package with main class
--   `testing:Test`.
-- + any additional `.smol` files.
-- Positive test-cases should compile and run successfully.

-- `tests/negative` should contain one or more folders; each is a test-category.
-- Each test category should contain one or more folders; each is a test-case.
-- Each negative test-case should contain:
-- + `test.smol`, a test file in the `testing` package with main class
--   `testing:Test`.
-- + any additional `.smol` files.
-- Negative test-cases should be rejected by the compiler gracefully. They
-- should not create any executable or output.

--------------------------------------------------------------------------------

local filter = arg[1]

--------------------------------------------------------------------------------

local function shell(command)
	local status, _, code = os.execute(command)
	if status == true then
		-- Lua 5.2 returns true|nil, reason, status
		return true, 0
	elseif status == nil then
		-- Lua 5.2 returns true|nil, reason, status
		return false, code
	end
	-- Lua 5.1 returns just the status code
	return status == 0, status
end

local function path(elements)
	return table.concat(elements, "\\")
end

local function shell_ls(directory)
	local contents = {}
	-- TODO: make this more portable and robust
	for line in io.popen("ls " .. directory, "r"):lines() do
		table.insert(contents, line)
	end
	return contents
end

-- RETURNS a set of paths to the files/folders within the given directory.
local function ls(directory, ext)
	local paths = {}
	for _, element in ipairs(shell_ls(directory)) do
		if not ext or element:sub(-(1 + #ext)) == "." .. ext then
			table.insert(paths, path {directory, element})
		end
	end
	return paths
end

--------------------------------------------------------------------------------

local function printHeader(text, symbol, align)
	symbol = symbol or "-"
	align = align or "left"

	local middle = " " .. text .. " "
	local remaining = 80 - #middle
	local left, right

	if align == "left" then
		left = 2
		right = remaining - left
	elseif align == "center" then
		left = math.floor(remaining / 2) - 1
		right = remaining - left
	else
		error "unknown alignment"
	end

	assert(left + #middle + right == 80 or #middle+4 >= 80)
	print("")
	print(symbol:rep(left) .. middle .. symbol:rep(right))
	print("")
end

-- Converts tabs to 4 spaces in a string that doesn't contain newlines
local function spaces(s)
	assert(not s:find("\n"))
	local out = ""
	for i = 1, #s do
		if s:sub(i, i) ~= "\t" then
			out = out .. s:sub(i, i)
		else
			repeat
				out = out .. " "
			until #out % 4 == 0
		end
	end
	return out
end

local function printBox(lines)
	local WIDTH = 80
	local bar = "+" .. string.rep("-", WIDTH-2) .. "+"
	local out = {bar}
	for _, line in ipairs(lines) do
		local row = spaces("|\t" .. line)
		row = row .. string.rep(" ", WIDTH - 1 - #row) .. "|"
		table.insert(out, row)
	end
	table.insert(out, bar)
	print(table.concat(out, "\n"))
end

--------------------------------------------------------------------------------

local tests = {}

-- Populate the negative tests
for _, group in ipairs(ls "tests\\negative") do
	for _, test in ipairs(ls(group)) do
		table.insert(tests, {
			id = "-" .. test,
			run = function()
				local sources = ls(test, "smol")
				local cmd = "\"\"./built/main\"\" interpet " .. table.concat(sources, " ") .. " --diagnostic-base " .. test  .. "\\ > " .. path {test, "err.actual"} .. " 2>&1"
				local _, code = shell(cmd)
				if code ~= 40 then
					return "fail", string.format("Expected code `40` but got `%d`.", code)
				end
				local _, code = shell("diff " .. path {test, "err.expected"} .. " " .. path{test, "err.actual"})
				if code ~= 0 then
					return "fail", string.format("Wrong output.")
				end
				return "pass"
			end,
		})
	end
end

--------------------------------------------------------------------------------

local passes = {}
local fails = {}

function PASS(p)
	assert(p.name)
	table.insert(passes, p)
	print("PASS: " .. p.name)
end

function FAIL(p)
	assert(p.name)
	assert(p.message)
	table.insert(fails, p)
	print("FAIL: " .. p.name)
end

local BEGIN_TIME = os.time()
function REPORT()
	printHeader("Detailed Results", "@", "center")

	for _, pass in ipairs(passes) do
		print("PASS: " .. pass.name)
	end

	for _, fail in ipairs(fails) do
		printBox {
			"FAIL: " .. fail.name,
			"\t" .. fail.message,
		}
		print()
	end

	printHeader("Summary Results", "@", "center")
	print("Passed: " .. #passes)
	print("Failed: " .. #fails)
	local elapsed = os.difftime(os.time(), BEGIN_TIME)
	print("Total time elapsed: " .. tostring(elapsed) .. " seconds")
	if #fails == 0 and #passes > 0 then
		print("Happy! :D")
		os.exit(0)
	else
		print("Sad. :(")
		os.exit(1)
	end
end

--------------------------------------------------------------------------------
local query = arg[1]

for _, test in ipairs(tests) do
	local matches = not query or test.id:find(query, 1, false)
	if matches then
		local result, message = test.run()
		assert(result == "fail" or result == "pass")
		if result == "pass" then
			PASS {
				name = test.id,
			}
		else
			assert(type(message) == "string")
			FAIL {
				name = test.id,
				message = message,
			}
			print()
		end
	end
end


-- (3) Report
REPORT()
