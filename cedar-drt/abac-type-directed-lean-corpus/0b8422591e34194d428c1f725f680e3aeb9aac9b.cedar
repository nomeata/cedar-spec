@B("7/")
@r("")
forbid(
  principal,
  action in [m::Action::""],
  resource == m::A00000::""
) when {
  ((true && (principal has "B")) && (principal has "n333333stpacWa")) && (m::A00000::"" has "A0")
};
