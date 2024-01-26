@A0("")
@qg("**")
permit(
  principal,
  action in [Action::""],
  resource in a::""
) when {
  (true && ((if (principal in principal) then 0 else 0) == (if ((ip("3636:3636:36ff:7e5f:ffff:7b7b:7b7b:7b7b")).isMulticast()) then (if false then 0 else (-9223372036854775808)) else (-(0))))) && (Action::"" in a::"")
};
