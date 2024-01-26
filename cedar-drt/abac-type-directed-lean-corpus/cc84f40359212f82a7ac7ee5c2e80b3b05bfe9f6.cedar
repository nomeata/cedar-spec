@A000("\02")
@r("")
forbid(
  principal is r::a,
  action in [r::Action::"action"],
  resource == r::a::">6\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true
};
