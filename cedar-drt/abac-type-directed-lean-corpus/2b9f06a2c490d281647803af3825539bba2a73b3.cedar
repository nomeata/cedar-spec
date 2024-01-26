forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if ([].containsAll([[]])) then (a::"A6" in Action::"action") else (!((ip("ff00:1:ffff:ffff:ffff:ffff:3736:36ff/126")).isIpv4())))) && ([].containsAll([if false then [] else [], [[]]]))) && (a::"A6" in resource)
};
