forbid(
  principal,
  action,
  resource == a::"6663DDDDDDDDDDDDDDDDDD\06"
) when {
  true && (a::"6663DDDDDDDDDDDDDDDDDD\06" in principal)
};
