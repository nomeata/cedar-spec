forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (if (action * 115) then (!action) else (principal == (a::"jj\0\0\0\0\0\0\0\0\0j" == a::"")))) && true
};
