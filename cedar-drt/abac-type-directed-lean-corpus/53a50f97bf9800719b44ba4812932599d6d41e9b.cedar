@A("\0\0\0")
@K("")
permit(
  principal,
  action in [Action::"action"],
  resource in r::"\0\0\0\0"
) when {
  true && (if (if (if true then false else false) then (!true) else (principal is r)) then ([[]].containsAll([true])) else true)
};
