@B("66666666666\0\0\0\0\0\0\0m\06")
@S("")
@m("")
@r("")
permit(
  principal == BR::"",
  action,
  resource == m::"\t"
) when {
  (true && ((decimal(principal["A"])).greaterThanOrEqual(if false then (if false then (decimal("390633414886726.416")) else (decimal("131942352.2326"))) else (principal["m"])))) && true
};
