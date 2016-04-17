//          Copyright Alexey Gerasimov(fan-tom) 2016.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
//

module modular;

import std.traits;
import std.conv;
import std.math;

// Exception thrown when operation cannot be done due to different modules
// of arguments
class ModulesAreNotTheSame:Exception{
	this(M1, M2)(M1 m1, M2 m2){
		super("Operands have different modules: "~m1.to!string~" and "~m2.to!string);
	}
}

// Function that implements mathematic modulo division in opposite to native
// D's '%' operator; particulary -1%4==-1 while -1.mod(4)==3. In other words
// the result of a%b always satisfies 0<=a%b<|b|
auto mod(D1, D2)(D1 divident, D2 divider) if(is(typeof(D1.init%D2.init)) && is(typeof(abs(D2.init))) && is(typeof(abs(D2.init)+D1.init%D2.init)))
in {
	assert(divider!=0, "Division by zero");
}
out(result) {
	assert(result>=0 && result<divider.abs, result.text);
}
body {
	auto absdiv=divider.abs;
	return (absdiv+divident%absdiv)%absdiv;
}
unittest {
	assert(15.mod(11)==4);
	assert((-1).mod(4)==3);
	assert((-5).mod(-4)==3);
	import std.bigint;
	assert(BigInt("-200").mod(5)==0);
	assert(BigInt(-11).mod(-8)==5);
}

// Calculates inverse for given value modulo mod using
// Extended Euclidean algorithm.
auto inverse(V, M)(in V value, in M mod)
in{
	assert(mod!=0, "Division by zero");
}
out(result){
	assert(value*result%mod==1, text(value,'*',result,'%',mod,'=',value*result%mod));
}
body{
	static if(is(typeof({ V v=M.init; })))
		//V can be assigned from M
		alias CommonType=Unqual!V;
	else if(is(typeof({ M m=V.init; })))
		//M can be assigned from V
		alias CommonType=Unqual!M;
	else
		static assert(false, "No common type for "~V.stringof~" and "~M.stringof);

	CommonType a=value, r, xn=1, yn=0, yn_, b=mod;
	while(a*b>0){
		r=b%a;
		yn_=yn;
		yn=xn;
		xn=yn_-b/a*xn;
		b=a;
		a=r;
	}
	if(b==1)
		return yn>=0?yn:mod+yn;
	throw new Error(text("Cannot calculate inverse for ",value," modulo ",mod));
}

// Struct ModInt represents number that is reminder of division on the module,
// which is also stored in structure.
// All operations are available, some of them are done using special methods,
// which do these operation more effective,
// such as fast multiplying and exponentiation
struct ModInt(V, M) if(is(typeof(V.init%M.init)))
{
	private:
		alias value_ this;
		V value_;
		M module_;

		auto inverse() const {
			return ModInt!(V,M)(value.inverse(mod),mod);
		}

		///Check if modules are the same
		///
		/// Params:
		///
		/// M =
		auto checkMod(M)(M m) const pure
		{
			return module_==m;
		}

		// Fast multiplication and exponentiation by consecutive doubling
		auto fastOp(string op, T)(T rhs_) const
		{
			debug op.writeln;

			static if(op=="*"){
				enum lower="+";
				ModInt t=ModInt(0,module_);
			}
			else static if(op=="^^"){
				enum lower="*";
				ModInt t=ModInt(1,module_);
			}
			else
				static assert(false, "This operation: "~op~" cannot be done by consecutive doubling");

			auto sign=rhs_<0?-1:1;
			debug{
				"t=".writeln(t.text);
				"sign=".writeln(sign.text);
			}
			//what if T is class???
			//maybe abs() is better?
			Unqual!T rhs=rhs_*sign;
			V res=value;
			debug{
				"rhs=".writeln(rhs.text);
				"res=".writeln(res.text);
			}
			while(rhs>0){
				if(rhs%2){
					mixin("t=t"~lower~"res;");
					//mixin("t"~lower~"=res");
					rhs-=1;
					debug{
						"\t\tt=".writeln(t.text);
						"\t\trhs=".writeln(rhs.text);
					}
				}
				mixin("res=res"~op~"2%module_;");
				rhs/=2;
				debug{
					"\tres=".writeln(res.text);
					"\trhs=".writeln(rhs.text);
				}
			}

			debug "return t=".writeln(t.text);
			static if(op=="*")
				return sign*t;
			else
				return sign>0?t:t.inverse;
		}

	public:

		//getter
		@property auto value() const pure nothrow
		{
			return value_;
		}
		
		//setter
		@property auto value(T)(T val_) nothrow
		{
			value_=val_;
		}

		//getter
		@property auto mod() const pure nothrow
		{
			return module_;
		}

		//setter
		@property auto mod(T)(T mod_) nothrow
		{
			module_=mod_;
		}

		//What can be reasonable init value for value_ and especially for module_?
		@disable this();

		this(in V val_, in M mod_){
			module_=mod_;
			value_=val_.mod(mod_);//(val_>=0?val_%mod:(mod-(-val_%mod)));
		}

		auto opOpAssign(string op, T)(in T rhs) if((op=="+" || op=="-") && isIntegral!(T))
		{
			mixin("value=value_"~op~"rhs;");
			return this;
		}

		const auto opBinary(string op, T: ModInt)(in T rhs) if((op=="+" || op=="-") )//&& is(T: ModInt))
		{
			if(checkMod(rhs.mod)){
				auto res=this;
				return res.opOpAssign!op(rhs);
			}
			throw new ModulesAreNotTheSame(mod, rhs.mod);
		}

		auto opOpAssign(string op, T: ModInt)(in T rhs) if((op=="+" || op=="-") )//&& is(T: ModInt))
		{
			if(checkMod(rhs.mod)){
				return ModInt(mixin("value"~op~"rhs.value"),mod);
			}
			throw new ModulesAreNotTheSame(mod, rhs.mod);
		}

		//Division is multiplication on inverse element a/b mod n =a*b^-1 mod n
		const auto opBinary(string op, T)(in T rhs) if((op=="/") && is(T: ModInt))
		{
			return this*rhs.inverse;
		}

		//Fast powering and multiplying
		auto opBinary(string op, T)(in T rhs) const if(op=="^^" || op=="*" )
		{
			static if(is(T: ModInt)){
				static if(op=="*")
					if(!checkMod(rhs.module_))
						throw new ModulesAreNotTheSame(mod, rhs.mod);
				auto arg=rhs.value;
			}
			else
				alias arg=rhs;
			auto res=ModInt(fastOp!op(arg), module_);
			return res;
			/*else
				assert(false, "Unsupported type: "~T.stringof);*/
		}
}
unittest{
	auto a=ModInt!(int,int)(10,4);
	assert(a.value==10%4);
	assert(a.mod==4);
	auto b=a+3;
	assert(b.value==(3+10%4)%4);
	assert(b.mod==4);
	assert(( a/b ).value==2);
	assert((ModInt!(int,uint)(15,11)^^3).value==9);
}

// Factory function to avoid explicit type indication using IFTI
auto modint(V, M)(V value, M mod){
	return ModInt!(V,M)(value,mod);
}
unittest{
	auto a=modint(10,4);
	assert(a.value==10%4);
	assert(a.mod==4);
	auto b=a+3;
	assert(b.value==(3+10%4)%4);
	assert(b.mod==4);
	import std.bigint;
	auto bigi=modint(BigInt("100"),3);
	assert(bigi.value==1);
	assert(bigi.mod==3);
}
