% use tail -n -1 results/100_samples/single/test_synth_6_10_dc_lib20_3_* | grep -Eo '[+-]?[0-9]+([.][0-9]+)+'
% to get data from raw files

iter = 10000;
load('EPS_SINGLE_20');
load('EPS_SINGLE_40');
load('EPS_SD_20');
load('EPS_SD_40');

A = EPS_SINGLE_20.times(1:30,:);
B = EPS_SINGLE_40.times(1:30,:);

C = EPS_SD_20;
D = EPS_SD_40;

stata = bootstrp(iter, @mean, A);
statb = bootstrp(iter, @mean, B);
statc = bootstrp(iter, @mean, C);
statd = bootstrp(iter, @mean, D);


resa = mean(stata);
resb = mean(statb);
resc = mean(statc);
resd = mean(statd);

meanci_a = bootci(iter, @mean, A);
meanci_b = bootci(iter, @mean, B);
meanci_c = bootci(iter, @mean, C);
meanci_d = bootci(iter, @mean, D);

resa = [resa; meanci_a];
resb = [resb; meanci_b];
resc = [resc; meanci_c];
resd = [resd; meanci_d];

resa = resa'
resb = resb'
resc = resc'
resd = resd'

% figure;
% hold;
% stat = bootstrp(iter, @mean, B);
% for i = 1:size(stat,2)
%     histogram(stat(:,i));
%     legendInfo{i} = [num2str(i)];
% end
% legend(legendInfo);
% stat = bootstrp(iter, @mean, EPS_PAR_PLAIN);
% histogram(stat);
% stat = bootstrp(iter, @mean, EPS_PAR_PORTS);
% histogram(stat);
% stat = bootstrp(iter, @mean, EPS_PAR_COMPS);
% histogram(stat);

% mean_eps_single_20 = mean(EPS_SINGLE_PLAIN_20)
% mean_eps_single_40 = mean(EPS_SINGLE_PLAIN_40)
% mean_eps_par_20 = mean(EPS_PAR_PLAIN_20)
% mean_eps_par_40 = mean(EPS_PAR_PLAIN_40)
% mean_eps_ports_20 = mean(EPS_PAR_PORTS_20)
% mean_eps_ports_40 = mean(EPS_PAR_PORTS_40)
% mean_eps_plain = mean(EPS_PAR_PLAIN)
% mean_eps_ports = mean(EPS_PAR_PORTS)
% mean_eps_comps = mean(EPS_PAR_COMPS)
% meanci_eps_single_20 = bootci(iter, @mean, EPS_SINGLE_PLAIN_20)
% meanci_eps_single_40 = bootci(iter, @mean, EPS_SINGLE_PLAIN_40)
% meanci_eps_par_20 = bootci(iter, @mean, EPS_PAR_PLAIN_20)
% meanci_eps_par_40 = bootci(iter, @mean, EPS_PAR_PLAIN_40)
% meanci_eps_ports_20 = bootci(iter, @mean, EPS_PAR_PORTS_20)
% meanci_eps_ports_40 = bootci(iter, @mean, EPS_PAR_PORTS_40)
% meanci_eps_plain = bootci(iter, @mean, EPS_PAR_PLAIN)
% meanci_eps_ports = bootci(iter, @mean, EPS_PAR_PORTS)
% meanci_eps_comps = bootci(iter, @mean, EPS_PAR_COMPS)


% err
% EPS_PAR_PORTS_40 = [EPS_PAR_PORTS_40 temp]
