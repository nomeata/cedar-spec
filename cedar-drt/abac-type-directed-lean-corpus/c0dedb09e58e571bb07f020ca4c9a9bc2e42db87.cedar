forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("38c3:c3c3:c3c3:c3c3:c3c3:bec3:c3c3:c3c3/66")) == (ip("195.0.0.0/30"))) then (if false then (ip("0.0.0.0")) else (ip("::7270:7865"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0")))) == (if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("c2f2:f236:3636:3636:3636:3636:36c3:c3c3")))))) && ((if ((ip("54.194.242.242")) == (ip("c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3:c3c3/66"))) then (if true then (ip("3636::1:c3c3:c3c3:ffff")) else (ip("0.0.0.0"))) else (ip("0.0.0.0"))) == (ip("0.0.0.0")))) && false
};
