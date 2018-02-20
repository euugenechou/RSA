# Eugene Chou
# euchou@ucsc.edu
# An implementation of RSA done in Python

import rsa
import sys
import math
import pickle
import random
import hashlib
import argparse
from fractions import gcd

parser = argparse.ArgumentParser(description = 'Runs RSA')
parser.add_argument('-e', help = 'encrypt', action = 'store_true', default = False)
parser.add_argument('-d', help = 'decrypt', action = 'store_true', default = False)
parser.add_argument('-i', help = 'input file', nargs = 1)
parser.add_argument('-o', help = 'output file (if not specified, stdout)', nargs = 1)
parser.add_argument('-g', help = 'generate a key of specific size; use with -o for base file name', nargs = 1)
parser.add_argument('-k', help = 'key file (required for encrypt, decrypt, sign, and verify)', nargs = 1)
parser.add_argument('-s', help = 'sign', action = 'store_true', default = False)
parser.add_argument('-v', help = 'verify', action = 'store_true', default = False)
args = parser.parse_args()

def checkIOArgs(i = False, o = False, k = False):
	if i and not args.i:
		raise Exception("Action requires Input File")
	if o and not args.o:
		raise Exception("Action requires Output File")
	if k and not args.k:
		raise Exception("Action requires Key File")

##### Number Theory #####
def modPow(base, power, m):
# Compute base ^ power mod m.
# Done efficiently (i.e. O(log(power)) time).
	if power == 1: 
		return base % m
	
	temp = 1
	while power > 0:
		if (power % 2 != 0): # if power is odd
			temp = (temp * base) % m
		power /= 2
		base = (base ** 2) % m

	return temp

def CRT(m, p, n, q):
# Chinese Remainder Theorem. 
# Calculates numbers a such that a = m mod p and b = n mod q.
	if gcd(p, q) != 1:
		print '%d and %d are not coprime' % (p, q)
	
	a = m * q * inverse(q, p)
	b = n * p * inverse(p, q)

	return (a + b) % (p * q)


def garnerCRT(m, p, n, q, qinverse):
# Chinese Remainder Theorem using Garner's formula for decrypting.
	if gcd(p, q) != 1:
		print '%d and %d are not coprime' % (p, q)

	return ((m - p) * qinverse % n * q + p) % (n * q)


def inverse(x, p):
    # Returns the modular inverse of x % p
    # Uses Extended Euclidean Algorithm
    if gcd(x, p) != 1:
        print "No modular inverse" # no modular inverse if x and p aren't coprime

    i, orig_i = p, x
    j, orig_j = 0, 1
    k, orig_k = 1, 0

    while i != 0:
    	quotient = orig_i // i
    	(orig_i, i) = (i, orig_i - quotient * i)
    	(orig_j, j) = (j, orig_j - quotient * j)
    	(orig_k, k) = (k, orig_k - quotient * k)

    return orig_j % p


def testPrime(p, chance_false):
# Test if p is prime. 
# Chance that p is composite should be less than chance_false. 
# An implementation of the Miller-Rabin Test.
	if p == 2: 	# 2 is exception
		return True

	if modPow(p, 1, 2) == 0: # check if p is even
		return False

	# loop number of witnesses such that chance_false is 3/4 chance
	for i in range(0, int(math.ceil(math.log(chance_false, 0.25)))):
		w = random.randint(2, p - 1) # generate witness such that 2 <= witness < p - 1
		a = p - 1 
		d = 0 # counter for power when dividing out 2s

		# divide a by 2 while ensuring it stays an integer
		while modPow(a, 1, 2) == 0:
			a = a // 2 
			d += 1

		# calculate mod of powers of two
		wa = modPow(w, a, p)
		while d > 0:
			next = modPow(wa, 2, p)
			if next == 1 and modPow(wa, 1, p) != p - 1 and modPow(wa, 1, p) != 1:
				return False
			wa = next
			d -= 1

		if wa != 1:
			return False

	# is prime if no violation of Fermat's little theorem
	return True


def getPrime(a, b):
	# Generates a prime between a and b.
    prime = False
    while not prime:
        p = random.randint(a, b)
        prime = testPrime(p, 0.01)
    return p

##### Encrypt/Decrypt/Keygen #####
def encrypt(msg, keypub):
	return modPow(msg, keypub[1], keypub[0])


def decrypt(msg, keyprivate):
    a = modPow(msg, keyprivate[5], keyprivate[3])
    b = modPow(msg, keyprivate[6], keyprivate[4])
    return garnerCRT(a, b, keyprivate[3], keyprivate[4], keyprivate[7])

def keyGen(keysize):
# Generates private and public key.
	# set p and q to correct keysize
	p = 2 ** (1 + keysize / 2) - 1 
	q = 2 ** (1 + keysize / 2) - 1

	# get primes of correct keysize
	while math.floor(math.log(p * q, 2)) > keysize:
		p = getPrime(2 ** (keysize / 2), 2 ** (1 + keysize / 2) - 1)
		q = getPrime(2 ** (keysize / 2), 2 ** (1 + keysize / 2) - 1)

	# setting private and public key components
	pinverseq = inverse(p, q)
	qinversep = inverse(q, p)
	e = 65536 + 1 % (p * q)
	d = inverse(e, (p - 1) * (q - 1))
	dmodp = d % (p - 1)
	dmodq = d % (q - 1)

	return ([p * q, e, d, p, q, dmodp, dmodq, qinversep, pinverseq], [p * q, e])


##### Signing/Verifying #####
def sign(inp, outp, key):
	keylen = math.log(k[0], 2)
	h = hashlib.sha256()
	blockify(int(keylen // 2), inp, h.update)   # Get hash for file
	h = h.hexdigest()

	def sign_block(h_block):
		h_block = "%x" % decrypt(int(h_block, 16), k)
		h_block = h_block.zfill(int(keylen // 4))	# Pad with zeros
		outp.write(h_block)
		print h_block
	blockifys(int(keylen // 4), h, sign_block)

	# Write the rest of the file
	outp.write("\n")
	inp.seek(0)
	for line in inp:
		outp.write(line)


def verify(inp, key):
	keylen = math.log(k[0], 2)
	hsigned = inp.readline()[:-1]	# Take off the trailing newline
	h2 = hashlib.sha256()
	blockify(int(keylen // 2), inp, h2.update)  # Get hash for rest of file
	h2 = h2.hexdigest()
	h = [""]
	
	def verify_block(x):
		print x
		x = int(x, 16)		# Convert to integer
		x = encrypt(x, k)	# Decrypt
		h[0] += "%x" % x 	# Append to hash

	blockifys(int(math.ceil(keylen / 4)), hsigned, verify_block)

	return h[0] == h2


##### Text/File Processing #####
def str_to_int(s):
# Converts string to integer.
	return int(''.join(("%x" % ord(c)).zfill(2) for c in s), 16)


def int_to_str(i):
# Converts integer to string.
    if i < 1:
        return ''

    strlen = int(math.ceil(math.log(i, 256)))
    s = [''] * strlen

    for x in reversed(range(0, strlen)):
        s[x] = chr(i & 255)
        i /= 256

    return ''.join(s)


def do_encrypt(inp, outp, key):
	keylen = math.log(k[0], 2)
	def encrypt_block(m):
		m = str_to_int(m)	# Convert to int
		m = "%x" % encrypt(m, key) # Encrypt and convert to hex
		m = m.zfill(int(math.ceil(keylen / 4.0)))	# Pad it to the correct length (hex if 4 bits per character)
		outp.write(m)
	blockify(int(keylen) // 8, inp, encrypt_block)


def do_decrypt(inp, outp, key):
	keylen = math.log(k[0], 2)
	def decrypt_block(m):
		m = int(m, 16)	# Convert from hex to integer
		m = decrypt(m, key)	# Decrypt
		m = int_to_str(m)	# Convert to ascii
		outp.write(m)
	blockify(int(math.ceil(keylen / 4.0)), inp, decrypt_block, "0")	# 4 bits per hex digit, padded with 0s


def blockify(blen, f, fn, fill = '\x00'):
# Breaks down large messages into chunks while reading file.
    cont = True
    while cont:
        b = f.read(blen)
        if len(b) < blen:
            if len(b) == 0:
                break
            cont = False
        fn(b.rjust(blen, fill))


def blockifys(blen, s, fn, fill = '\x00'):
	while len(s) > 0:
		b = s[:blen]
		# print "block: <%s>" % b
		fn(b.rjust(blen, fill))
		s = s[blen:]


def dumpKey(key, file):
# Pickles and dumps serialized key to a file.
	with open(file, 'wb') as dumpfile:
		pickle.dump(key, dumpfile)


def loadKey(file):
# Unpickles serialized key.
	with open(file, 'rb') as loadfile:
		key = pickle.load(loadfile)
	return key

##### Main Control Flow #####
if __name__ == '__main__':
	if not len(sys.argv) > 1:
		print 'type "-h" or "--help" to see program usage'

	if args.i:
		inp = open(args.i[0], "r")
	if args.o:
		outp = open(args.o[0], "w")
	else:
		outp = sys.stdout
	if args.k:
		k = loadKey(args.k[0])

	if args.e:
		checkIOArgs(i = True, o = True)
		do_encrypt(inp, outp, k)
	elif args.d:
		checkIOArgs(i = True, k = True)
		do_decrypt(inp, outp, k)
	elif args.g:
		checkIOArgs(o = True)
		keyprivate, keypub = keyGen(int(args.g[0]))
		dumpKey(keyprivate, args.o[0])
		dumpKey(keypub, args.o[0] + ".pub")
	elif args.s:
		checkIOArgs(i = True, o = True, k = True)
		do_sign(inp, outp, k)
	elif args.v:
		checkIOArgs(i = True, k = True)
		if do_verify(inp, k):
			print "Verified"
		else:
			print "Verification failed"